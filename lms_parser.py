"""
Парсер календаря дедлайнов и БРС (Балльно-рейтинговой системы) из СДО РАНХиГС (lms.ranepa.ru).

Поддерживает:
1. Импорт и нормализацию iCal-ссылок календаря (export_execute.php).
2. Разовую (эфемеpную) выгрузку БРС, оценок по предметам и авто-получение ссылки календаря
   по логину/паролю СДО без сохранения пароля и с мгновенным завершением сессии (logout).
3. Обработку выгрузки БРС от браузерного расширения (ranepa-moodle-theme) по 6-значному коду.
4. Автоматическую отметку проверенных в БРС заданий как «Сдано» в списке дедлайнов.
"""

import asyncio
from concurrent.futures import ThreadPoolExecutor
import html as html_lib
import http.cookiejar
import logging
import re
import ssl
import urllib.parse
import urllib.request
from datetime import datetime, timedelta, timezone
from typing import Optional

logger = logging.getLogger(__name__)

MSK = timezone(timedelta(hours=3))

DEFAULT_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36",
    "Accept": "text/calendar,text/plain,text/html,*/*;q=0.8",
}

_ssl_ctx = ssl.create_default_context()
_ssl_ctx.check_hostname = False
_ssl_ctx.verify_mode = ssl.CERT_NONE


def normalize_lms_calendar_url(raw_url: str) -> str:
    """
    Проверяет ссылку на экспорт календаря Moodle (lms.ranepa.ru) и принудительно
    выставляет preset_what=all и preset_time=recentupcoming (все события на 60 дней),
    даже если студент случайно выбрал 'Эта неделя' или 'События курса'.
    """
    if not raw_url or not isinstance(raw_url, str):
        raise ValueError("Пустая ссылка на календарь")

    url = raw_url.strip().replace("&amp;", "&")
    parsed = urllib.parse.urlparse(url)

    if not parsed.scheme or parsed.scheme not in ("http", "https"):
        raise ValueError("Ссылка должна начинаться с https://")

    if "lms.ranepa.ru" not in parsed.netloc.lower():
        raise ValueError("Поддерживаются только ссылки календаря СДО РАНХиГС (lms.ranepa.ru)")

    if "export_execute.php" not in parsed.path:
        raise ValueError(
            "Это не ссылка экспорта календаря. На странице экспорта нажмите «Получить адрес календаря» и скопируйте ссылку с export_execute.php"
        )

    qs = urllib.parse.parse_qs(parsed.query)
    userid = qs.get("userid", [None])[0]
    authtoken = qs.get("authtoken", [None])[0]

    if not userid or not authtoken:
        raise ValueError("В ссылке отсутствуют обязательные параметры userid или authtoken")

    clean_query = urllib.parse.urlencode({
        "userid": userid,
        "authtoken": authtoken,
        "preset_what": "all",
        "preset_time": "recentupcoming",
    })

    return f"https://lms.ranepa.ru/calendar/export_execute.php?{clean_query}"


def _download_ics(url: str, timeout: float = 15.0) -> str:
    req = urllib.request.Request(url, headers=DEFAULT_HEADERS)
    with urllib.request.urlopen(req, context=_ssl_ctx, timeout=timeout) as resp:
        raw = resp.read()
        text = raw.decode("utf-8", errors="replace")
        if "BEGIN:VCALENDAR" not in text:
            raise ValueError("Сервер СДО не вернул корректный iCal-календарь (проверьте токен в ссылке)")
        return text


def _unescape_ics(val: str) -> str:
    if not val:
        return ""
    return (
        val.replace("\\n", "\n")
        .replace("\\N", "\n")
        .replace("\\,", ",")
        .replace("\\;", ";")
        .replace("\\\\", "\\")
        .replace("\xa0", " ")
        .strip()
    )


def _strip_tags(raw_html: str) -> str:
    if not raw_html:
        return ""
    text = re.sub(r"<br\s*/?>", "\n", raw_html, flags=re.IGNORECASE)
    text = re.sub(r"</p\s*>", "\n", text, flags=re.IGNORECASE)
    text = re.sub(r"<[^>]+>", "", text)
    text = html_lib.unescape(text).replace("\xa0", " ")
    lines = [" ".join(line.split()) for line in text.splitlines()]
    return "\n".join(line for line in lines if line).strip()


def _parse_float_score(val_str: str) -> Optional[float]:
    if not val_str:
        return None
    clean = val_str.strip().replace("\xa0", "").replace(" ", "").replace(",", ".")
    if clean in ("-", "—", "–", ""):
        return None
    m = re.search(r"[-+]?\d+(?:\.\d+)?", clean)
    if not m:
        return None
    try:
        return round(float(m.group(0)), 2)
    except Exception:
        return None


def parse_course_fullname(full_name: str) -> dict:
    """
    Разбирает строку вида:
    'Литература [1 семестр] [Иванова И.И.] [101-ИИ-26]'
    """
    raw = " ".join(html_lib.unescape(full_name or "").replace("\xa0", " ").split())
    brackets = re.findall(r"\[([^\]]+)\]", raw)
    clean_title = re.sub(r"\s*\[[^\]]+\]", "", raw).strip()

    semester = ""
    teacher = ""
    group = ""

    for b in brackets:
        b_str = b.strip()
        if "семестр" in b_str.lower() or "курс" in b_str.lower():
            semester = b_str
        elif re.search(r"\d{2,3}[-—–][А-Яа-яA-Za-z]+[-—–]\d{2}", b_str):
            group = b_str
        elif "." in b_str or len(b_str.split()) >= 2:
            if not teacher:
                teacher = b_str
            elif not group:
                group = b_str
        else:
            if not group:
                group = b_str

    return {
        "full_name": raw,
        "discipline": clean_title or raw,
        "semester": semester,
        "teacher": teacher,
        "group": group,
    }


def classify_brs_rating(score: Optional[float]) -> dict:
    """
    Возвращает статус по официальной шкале БРС РАНХиГС:
    0 - 54: Неудовлетворительно / Незачтено (F)
    55 - 64: Удовлетворительно / Зачтено (E)
    65 - 74: Хорошо (D)
    75 - 84: Хорошо (C)
    85 - 94: Отлично (B)
    95 - 100: Отлично (A)
    """
    pts = score if score is not None else 0.0
    if pts >= 95:
        return {"grade_5": 5, "label": "Отлично", "binary": "Зачтено", "ects": "A", "next_target": None, "points_to_next": 0, "next_label": "Максимум"}
    if pts >= 85:
        return {"grade_5": 5, "label": "Отлично", "binary": "Зачтено", "ects": "B", "next_target": 95, "points_to_next": round(95 - pts, 2), "next_label": "ECTS A (95)"}
    if pts >= 75:
        return {"grade_5": 4, "label": "Хорошо", "binary": "Зачтено", "ects": "C", "next_target": 85, "points_to_next": round(85 - pts, 2), "next_label": "Отлично (85)"}
    if pts >= 65:
        return {"grade_5": 4, "label": "Хорошо", "binary": "Зачтено", "ects": "D", "next_target": 85, "points_to_next": round(85 - pts, 2), "next_label": "Отлично (85)"}
    if pts >= 55:
        return {"grade_5": 3, "label": "Удовлетворительно", "binary": "Зачтено", "ects": "E", "next_target": 65, "points_to_next": round(65 - pts, 2), "next_label": "Хорошо (65)"}
    return {
        "grade_5": 2,
        "label": "Неудовлетворительно",
        "binary": "Незачтено",
        "ects": "F",
        "next_target": 55,
        "points_to_next": round(55 - pts, 2),
        "next_label": "Автомат / Зачёт (55)",
    }


def parse_overview_html(ov_html: str) -> tuple[Optional[str], list[dict]]:
    """
    Парсит страницу /grade/report/overview/index.php.
    Возвращает (user_id, список курсов).
    """
    if not ov_html:
        return None, []

    user_id = None
    m_uid = re.search(r'"userId"\s*:\s*(\d+)', ov_html)
    if m_uid:
        user_id = m_uid.group(1)

    courses = []
    row_pattern = re.compile(
        r'<tr[^>]*id="grade-report-overview-[^"]*"[^>]*>(.*?)</tr>',
        re.DOTALL | re.IGNORECASE,
    )

    for row_html in row_pattern.findall(ov_html):
        c0_m = re.search(r'<td[^>]*class="[^"]*\bc0\b[^"]*"[^>]*>(.*?)</td>', row_html, re.DOTALL)
        c1_m = re.search(r'<td[^>]*class="[^"]*\bc1\b[^"]*"[^>]*>(.*?)</td>', row_html, re.DOTALL)
        if not c0_m:
            continue

        c0_inner = c0_m.group(1)
        c1_inner = c1_m.group(1) if c1_m else "-"

        link_m = re.search(r'href="([^"]*course/user\.php\?[^"]*)"', c0_inner)
        course_id = None
        if link_m:
            href = html_lib.unescape(link_m.group(1))
            qs = urllib.parse.parse_qs(urllib.parse.urlparse(href).query)
            course_id = qs.get("id", [None])[0]
            if not user_id and qs.get("user", [None])[0]:
                user_id = qs.get("user", [None])[0]

        raw_name = _strip_tags(c0_inner)
        if not raw_name:
            continue

        score_str = _strip_tags(c1_inner) or "-"
        score_val = _parse_float_score(score_str)
        meta = parse_course_fullname(raw_name)
        rating = classify_brs_rating(score_val)

        courses.append({
            "course_id": str(course_id) if course_id else "",
            "full_name": meta["full_name"],
            "discipline": meta["discipline"],
            "semester": meta["semester"],
            "teacher": meta["teacher"],
            "group": meta["group"],
            "total_score": score_val,
            "total_score_str": score_str,
            "rating": rating,
            "tku_score": None,
            "tku_max": 60,
            "db_score": None,
            "db_max": 30,
            "pa_score": None,
            "pa_max": 40,
            "planned_pairs": None,
            "items": [],
        })

    return user_id, courses


def parse_course_gradebook_html(course_html: str) -> dict:
    """
    Парсит страницу оценок конкретного курса (/course/user.php?mode=grade&id=...&user=...).
    Извлекает баллы по категориям (Текущий контроль, Дополнительные баллы, Промежуточная аттестация)
    и список всех контрольных точек / заданий с оценками и отзывами.
    """
    result = {
        "tku_score": None,
        "tku_max": 60,
        "db_score": None,
        "db_max": 30,
        "pa_score": None,
        "pa_max": 40,
        "total_score": None,
        "total_score_str": "-",
        "grade_5_str": "-",
        "ects_str": "-",
        "items": [],
    }
    if not course_html:
        return result

    table_m = re.search(
        r'<table[^>]*class="[^"]*\buser-grade\b[^"]*"[^>]*>(.*?)</table>',
        course_html,
        re.DOTALL | re.IGNORECASE,
    )
    if not table_m:
        return result

    tbody_html = table_m.group(1)
    tr_list = re.findall(r"<tr[^>]*>(.*?)</tr>", tbody_html, re.DOTALL | re.IGNORECASE)

    current_category = "Общее"

    for tr_inner in tr_list:
        # 1. Если в строке нет ячейки оценки (column-grade) — это заголовок категории или шапка таблицы
        if "column-grade" not in tr_inner:
            if "column-itemname" in tr_inner:
                cat_text = _strip_tags(tr_inner)
                if cat_text:
                    if "текущий контроль" in cat_text.lower():
                        current_category = "Текущий контроль"
                    elif "дополнительные баллы" in cat_text.lower():
                        current_category = "Дополнительные баллы"
                    elif "промежуточная аттестация" in cat_text.lower():
                        current_category = "Промежуточная аттестация"
            continue

        # 2. Ищем ячейку названия элемента (column-itemname)
        name_m = re.search(
            r'<(?:th|td)[^>]*class="[^"]*\bcolumn-itemname\b[^"]*"[^>]*>(.*?)</(?:th|td)>',
            tr_inner,
            re.DOTALL | re.IGNORECASE,
        )
        if not name_m:
            continue

        name_cell = name_m.group(1)

        # Тип элемента (Задание, Оценка вне СДО, Вычисляемая оценка, Тест и т.д.)
        type_m = re.search(r'<span[^>]*class="[^"]*text-uppercase[^"]*"[^>]*>(.*?)</span>', name_cell, re.DOTALL)
        item_type = _strip_tags(type_m.group(1)) if type_m else ""

        title_m = re.search(r'<div[^>]*class="[^"]*\browtitle\b[^"]*"[^>]*>(.*?)</div>', name_cell, re.DOTALL)
        item_title = _strip_tags(title_m.group(1)) if title_m else _strip_tags(name_cell)

        link_m = re.search(r'href="([^"]+)"', name_cell)
        item_url = html_lib.unescape(link_m.group(1)) if link_m else ""

        def _extract_col(col_class: str) -> str:
            m = re.search(
                rf'<td[^>]*class="[^"]*\b{col_class}\b[^"]*"[^>]*>(.*?)</td>',
                tr_inner,
                re.DOTALL | re.IGNORECASE,
            )
            return _strip_tags(m.group(1)) if m else "-"

        weight_str = _extract_col("column-weight")
        grade_str = _extract_col("column-grade")
        range_str = _extract_col("column-range").replace("–", "-")
        pct_str = _extract_col("column-percentage")
        feedback_str = _extract_col("column-feedback")
        if feedback_str == "-":
            feedback_str = ""

        # Проверка прикрепленного файла ответа студента и статуса отправки
        has_file = bool(re.search(
            r'(?:pluginfile\.php|assignsubmission|fa-file|\.(?:docx?|pdf|zip|rar|pptx?|xlsx?|txt|png|jpg|7z))\b',
            tr_inner,
            re.IGNORECASE
        ))
        is_submitted = has_file or bool(re.search(
            r'(?:сдано|отправлено|ответ\s+отправлен|требует\s+оценки|submitted)',
            tr_inner,
            re.IGNORECASE
        ))

        grade_val = _parse_float_score(grade_str)
        title_lower = item_title.lower()

        # Проверяем итоговые вычисляемые строки
        if "итого в категории" in title_lower or item_type.lower() == "вычисляемая оценка":
            if "текущий контроль" in title_lower:
                result["tku_score"] = grade_val
                continue
            elif "дополнительные баллы" in title_lower:
                result["db_score"] = grade_val
                continue
            elif "промежуточная аттестация" in title_lower:
                result["pa_score"] = grade_val
                continue
            elif "сумма баллов по дисциплине" in title_lower or "итоговая оценка за курс" in title_lower:
                if grade_val is not None:
                    result["total_score"] = grade_val
                    result["total_score_str"] = grade_str
                continue
            elif "5-балльной" in title_lower:
                result["grade_5_str"] = grade_str
                continue
            elif "ects" in title_lower:
                result["ects_str"] = grade_str
                continue

        if not item_title or item_title.lower() == "элемент оценивания":
            continue

        result["items"].append({
            "title": item_title,
            "item_type": item_type or "Элемент",
            "category": current_category,
            "weight": weight_str,
            "grade": grade_val,
            "grade_str": grade_str,
            "range": range_str,
            "percentage": pct_str,
            "feedback": feedback_str,
            "url": item_url,
            "has_file": has_file,
            "is_submitted": is_submitted,
        })

    return result


def parse_course_assign_index_html(assign_html: str) -> list[dict]:
    """
    Парсит страницу со списком всех заданий курса (/mod/assign/index.php?id=...).
    Извлекает название задания, статус отправки ('Сдано для оценивания', 'Ответ отправлен'),
    наличие прикрепленного файла и признак просроченности из самого СДО.
    """
    if not assign_html or "<table" not in assign_html:
        return []
    items = []
    tr_matches = re.findall(r"<tr[^>]*>(.*?)</tr>", assign_html, re.DOTALL | re.IGNORECASE)
    for tr in tr_matches:
        if "cell" not in tr and "<td" not in tr:
            continue
        title_m = re.search(r'<a[^>]*href="([^"]*mod/assign/view\.php[^"]*)"[^>]*>(.*?)</a>', tr, re.IGNORECASE | re.DOTALL)
        if not title_m:
            continue
        url = html_lib.unescape(title_m.group(1))
        title = _strip_tags(title_m.group(2)).strip()
        if not title:
            continue

        tr_text = _strip_tags(tr).lower()
        has_file = bool(re.search(
            r'(?:pluginfile\.php|assignsubmission|fa-file|\.(?:docx?|pdf|zip|rar|pptx?|xlsx?|txt|png|jpg|jpeg|7z|tar|gz))\b',
            tr,
            re.IGNORECASE
        ))
        has_negative = any(neg in tr_text for neg in [
            "не отправлено", "нет ответа", "не сдано", "не оценено и не отправлено", "черновик", "draft", "no submission"
        ])
        has_positive = any(pos in tr_text for pos in [
            "отправлен", "сдан", "оценен", "требует оценки", "submitted", "graded", "внесено в ведомость"
        ])
        is_submitted = (has_file or has_positive) and not has_negative
        is_overdue = (
            not is_submitted
            and any(ov in tr_text for ov in [
                "просрочено", "срок сдачи истек", "overdue", "срок истек"
            ])
        )

        items.append({
            "title": title,
            "url": url,
            "has_file": has_file,
            "is_submitted": is_submitted,
            "is_overdue": is_overdue,
        })
    return items


def _SelectActiveGroup(courses: list[dict]) -> str:
    """
    Определяет актуальную (текущую) группу студента из списка его курсов в СДО.
    Например, если есть курсы '101-ИСП-26', '201-ИСП-25' и '401-ИСП-23',
    выбирает группу с максимальным номером курса ('401-ИСП-23').
    """
    groups = [c["group"] for c in courses if c.get("group")]
    if not groups:
        return ""
    unique_groups = sorted(set(groups), key=lambda g: (int(re.match(r"^(\d+)", g).group(1)) if re.match(r"^(\d+)", g) else 0, g), reverse=True)
    return unique_groups[0]


def _normalize_match_text(s: str) -> str:
    if not s:
        return ""
    # Приводим похожие латинские/кириллические буквы к единому виду (например Doсker / Docker)
    homoglyphs = str.maketrans({
        "c": "с", "a": "а", "e": "е", "o": "о", "p": "р", "x": "х", "y": "у", "k": "к",
    })
    cleaned = s.lower().replace("ё", "е").replace("\xa0", " ").translate(homoglyphs)
    cleaned = re.sub(r"^(мдк|опц|оп|оуд|одб|огсэ|сгц|ен|пм|уп|пп)[\.\d\s_-]+", "", cleaned, flags=re.IGNORECASE)
    cleaned = re.sub(r"[^\w\dа-яё]+", " ", cleaned)
    return " ".join(cleaned.split())


# Плановое количество пар берётся из учебного плана КОНКРЕТНОГО профиля
# (специальность + год поступления), см. backend/services/curriculum.py.
# Общая база планов: backend/curricula/*.json (python -m backend.scripts.fetch_curricula).


def get_curriculum_planned_pairs(
    discipline: str,
    semester_str: str = "",
    custom_curriculum: Optional[dict] = None,
    course_group: str = "",
) -> Optional[int]:
    """Совместимость: плановые пары по переданному плану (без глобального справочника)."""
    from backend.services.curriculum import planned_pairs_for_course

    if not isinstance(custom_curriculum, dict) or not isinstance(custom_curriculum.get("disciplines"), dict):
        return None
    return planned_pairs_for_course(custom_curriculum, discipline, semester_str, course_group=course_group)


def parse_eljur_attendance_file(file_bytes: bytes, filename: str = "") -> dict:
    """
    Парсит выгруженную из Eljur таблицу посещаемости (.xlsx или .csv).
    Возвращает:
    {
      "header": "Посещаемость: ... / I семестр",
      "semester": "1 семестр",
      "subjects": [
        {
          "raw_name": "МДК.01.03 Безопасность компьютерных сетей",
          "code": "МДК.01.03",
          "discipline": "Безопасность компьютерных сетей",
          "total_missed": 3,
          "sick_b": 0,
          "excused_u": 0,
          "unexcused_n": 3
        },
        ...
      ]
    }
    """
    from io import BytesIO, StringIO
    import csv

    rows: list[list] = []
    fn_lower = (filename or "").lower()

    if fn_lower.endswith(".csv") or fn_lower.endswith(".tsv") or fn_lower.endswith(".txt"):
        text = ""
        for enc in ("utf-8-sig", "utf-8", "cp1251", "latin-1"):
            try:
                text = file_bytes.decode(enc)
                break
            except Exception:
                continue
        if not text:
            raise ValueError("Не удалось прочитать текстовый файл посещаемости")
        delim = ";" if ";" in text[:400] else ("\t" if "\t" in text[:400] else ",")
        reader = csv.reader(StringIO(text), delimiter=delim)
        for r in reader:
            rows.append(r)
    else:
        try:
            import openpyxl
            wb = openpyxl.load_workbook(BytesIO(file_bytes), data_only=True)
            ws = wb.active
            for r in ws.iter_rows(values_only=True):
                rows.append(list(r))
        except Exception as e:
            raise ValueError(f"Не удалось открыть Excel-таблицу посещаемости (.xlsx): {e}")

    if not rows:
        raise ValueError("Таблица посещаемости пуста")

    header_str = ""
    semester_str = ""
    subjects = []

    # Определяем индексы колонок (обычно: 0=Предмет, 1=Всего, 2=Б, 3=У, 4=Н)
    col_total = 1
    col_b = 2
    col_u = 3
    col_n = 4

    for r in rows:
        if not r or all(c is None or str(c).strip() == "" for c in r):
            continue
        first_cell = str(r[0] or "").strip()

        if "посещаемость" in first_cell.lower() and not header_str:
            # Убираем ФИО студента из заголовка для приватности, оставляем группу и семестр
            m_sem = re.search(r"/\s*(.+)$", first_cell)
            if m_sem:
                semester_str = m_sem.group(1).strip()
            m_grp = re.search(r"\(([^)]+)\)", first_cell)
            grp_part = m_grp.group(1).strip() if m_grp else ""
            header_str = " · ".join(p for p in (grp_part, semester_str) if p) or "Таблица Eljur"
            continue

        # Проверяем строку заголовков столбцов ('Всего', 'Б', 'У', 'Н')
        cells_str = [str(c or "").strip().upper() for c in r]
        if "ВСЕГО" in cells_str and "Н" in cells_str:
            for idx_c, c_val in enumerate(cells_str):
                if c_val == "ВСЕГО":
                    col_total = idx_c
                elif c_val == "Б":
                    col_b = idx_c
                elif c_val == "У":
                    col_u = idx_c
                elif c_val == "Н":
                    col_n = idx_c
            continue

        if not first_cell:
            continue
        low_first = first_cell.lower()
        if low_first.startswith("пропущено") or low_first == "итого" or low_first == "предмет":
            continue

        def _to_int(idx_col: int) -> int:
            if idx_col >= len(r) or r[idx_col] is None:
                return 0
            try:
                return int(float(str(r[idx_col]).strip().replace(",", ".")))
            except Exception:
                return 0

        code_m = re.match(r"^((?:МДК|ОПЦ|ОП|ОУД|ОДБ|ОГСЭ|СГЦ|ЕН|ПМ|УП|ПП)(?:\.[А-Яа-я0-9]+)+)\s+(.*)$", first_cell, re.IGNORECASE)
        if code_m:
            code_str = code_m.group(1).strip()
            disc_clean = code_m.group(2).strip()
        else:
            code_str = ""
            disc_clean = first_cell

        subjects.append({
            "raw_name": first_cell,
            "code": code_str,
            "discipline": disc_clean,
            "total_missed": _to_int(col_total),
            "sick_b": _to_int(col_b),
            "excused_u": _to_int(col_u),
            "unexcused_n": _to_int(col_n),
        })

    if not subjects:
        raise ValueError("В загруженном файле не найдены строки дисциплин с посещаемостью")

    return {
        "header": header_str,
        "semester": semester_str,
        "updated_at": datetime.now(MSK).strftime("%d.%m.%Y %H:%M"),
        "subjects": subjects,
    }


def parse_curriculum_pdf_bytes(pdf_bytes: bytes) -> dict:
    """Парсит PDF учебного плана КМПО (оба формата выгрузки), см. curriculum.parse_curriculum_pdf."""
    from backend.services.curriculum import parse_curriculum_pdf

    return parse_curriculum_pdf(pdf_bytes)


def _main_student_group(courses: list[dict]) -> str:
    from collections import Counter

    current = [c.get("group") for c in courses if c.get("group") and c.get("is_current", True)]
    pool = current or [c.get("group") for c in courses if c.get("group")]
    return Counter(pool).most_common(1)[0][0] if pool else ""


def apply_attendance_and_curriculum_to_courses(
    courses: list[dict],
    eljur_attendance: Optional[dict] = None,
    custom_curriculum: Optional[dict] = None,
    curriculum_plan_id: Optional[str] = None,
) -> dict:
    """
    Обогащает каждый курс из БРС:
    1. planned_pairs — плановое количество пар по учебному плану ЭТОГО профиля
       (свой PDF → выбранный план из общей базы → авто-подбор по группе и дисциплинам).
    2. eljur_attendance — пропуски из загруженной таблицы Eljur (Всего, Б, У, Н).
    Возвращает информацию о применённом плане: {id, label, source, source_url}.
    """
    from backend.services.curriculum import plan_label, planned_pairs_for_course, resolve_plan_for_user

    info: dict = {"id": None, "label": "", "source": "", "source_url": ""}
    if not courses:
        return info

    group = _main_student_group(courses)
    current_discs = [c.get("discipline", "") for c in courses if c.get("is_current", True)]
    plan, source = resolve_plan_for_user(
        {"custom_curriculum": custom_curriculum, "curriculum_plan_id": curriculum_plan_id},
        group=group,
        brs_disciplines=current_discs,
    )
    if plan:
        info = {
            "id": plan.get("id") if source != "custom" else "custom",
            "label": plan_label(plan) or "Загруженный учебный план",
            "source": source,
            "source_url": plan.get("source_url", ""),
        }

    eljur_subjects = (eljur_attendance or {}).get("subjects") if isinstance(eljur_attendance, dict) else None

    for course in courses:
        disc = course.get("discipline", "")
        sem = course.get("semester", "")
        planned = planned_pairs_for_course(plan, disc, sem, course_group=course.get("group", ""), user_group=group)
        course["planned_pairs"] = planned

        course.pop("eljur_attendance", None)
        if eljur_subjects:
            c_norm = _normalize_match_text(disc)
            matched_subj = None
            for subj in eljur_subjects:
                s_norm = _normalize_match_text(subj.get("discipline", "") or subj.get("raw_name", ""))
                if not s_norm or not c_norm:
                    continue
                if s_norm == c_norm or (len(s_norm) > 10 and (s_norm in c_norm or c_norm in s_norm)):
                    matched_subj = subj
                    break
            if matched_subj:
                course["eljur_attendance"] = {
                    "code": matched_subj.get("code", ""),
                    "total_missed": matched_subj.get("total_missed", 0),
                    "sick_b": matched_subj.get("sick_b", 0),
                    "excused_u": matched_subj.get("excused_u", 0),
                    "unexcused_n": matched_subj.get("unexcused_n", 0),
                }
    return info


def apply_brs_grades_to_notes(notes_dict: dict[str, dict], courses: list[dict]) -> int:
    """
    Сопоставляет проверенные задания из БРС с дедлайнами из календаря СДО.
    1. Если задание уже есть в notes_dict (из .ics календаря), помечает его как выполненное (completed=True)
       и прикрепляет полученный балл (lms_grade), максимум (lms_range) и отзыв преподавателя (lms_feedback).
    2. Если проверенного задания из текущего курса БРС нет в .ics календаре (например, старые работы за сентябрь-октябрь,
       лекции, тесты или контрольные точки), автоматически добавляет его в notes_dict как сданную работу СДО,
       чтобы студент видел абсолютно все свои сданные работы, оценки и отзывы преподавателей.
    """
    if notes_dict is None or not courses:
        return 0

    # Строим список всех проверенных заданий из БРС:
    # (course, cid, item_idx, disc_norm, full_norm, title_norm, item)
    graded_entries = []
    for c_idx, course in enumerate(courses):
        cid = str(course.get("course_id") or f"c{c_idx}")
        disc_norm = _normalize_match_text(course.get("discipline", ""))
        full_norm = _normalize_match_text(course.get("full_name", ""))
        for i_idx, item in enumerate(course.get("items") or []):
            if item.get("grade") is not None or item.get("has_file") or item.get("is_submitted"):
                title_norm = _normalize_match_text(item.get("title", ""))
                if title_norm:
                    graded_entries.append((course, cid, i_idx, disc_norm, full_norm, title_norm, item))

    if not graded_entries:
        return 0

    matched_entry_ids: set[tuple[str, int]] = set()
    auto_completed = 0

    # Шаг 1. Сопоставляем существующие заметки из календаря (.ics) с оценками из БРС
    for key, note in list(notes_dict.items()):
        if not isinstance(note, dict):
            continue
        if not (str(key).startswith("lms_") or note.get("source") == "lms"):
            continue
        # Пропускаем ранее сгенерированные синтетические записи БРС — мы обновим их ниже
        if str(key).startswith("lms_brs_"):
            continue

        note_title_norm = _normalize_match_text(note.get("text", ""))
        note_disc_norm = _normalize_match_text((note.get("lesson") or {}).get("discipline", ""))
        if not note_title_norm:
            continue

        matched_tuple = None
        for course, cid, i_idx, disc_norm, full_norm, item_title_norm, item in graded_entries:
            disc_ok = (
                not note_disc_norm
                or not disc_norm
                or disc_norm in note_disc_norm
                or note_disc_norm in disc_norm
                or note_disc_norm in full_norm
            )
            if not disc_ok:
                continue

            if (
                note_title_norm == item_title_norm
                or (len(note_title_norm) > 10 and note_title_norm in item_title_norm)
                or (len(item_title_norm) > 10 and item_title_norm in note_title_norm)
            ):
                matched_tuple = (course, cid, i_idx, item)
                break

        if matched_tuple:
            course, cid, i_idx, matched_item = matched_tuple
            matched_entry_ids.add((cid, i_idx))
            is_done = matched_item.get("grade") is not None or matched_item.get("has_file") or matched_item.get("is_submitted")
            if is_done:
                note["completed"] = True
                note["has_attached_file"] = bool(matched_item.get("has_file"))
                note["lms_overdue"] = False
            note["lms_grade"] = matched_item.get("grade_str", "")
            note["lms_range"] = matched_item.get("range", "0-100")
            note["lms_category"] = matched_item.get("category", "")
            note["lms_item_type"] = matched_item.get("item_type", "")
            if matched_item.get("feedback"):
                note["lms_feedback"] = matched_item.get("feedback", "")
            if course.get("teacher") and isinstance(note.get("lesson"), dict) and not note["lesson"].get("teacher"):
                note["lesson"]["teacher"] = course.get("teacher", "")
            auto_completed += 1

    # Шаг 1.1 Сопоставляем оставшиеся незавершенные заметки со списком заданий курса (assign_items)
    for key, note in list(notes_dict.items()):
        if not isinstance(note, dict) or note.get("completed"):
            continue
        if not (str(key).startswith("lms_") or note.get("source") == "lms"):
            continue
        note_title_norm = _normalize_match_text(note.get("text", ""))
        note_disc_norm = _normalize_match_text((note.get("lesson") or {}).get("discipline", ""))
        if not note_title_norm:
            continue

        for course in courses:
            disc_norm = _normalize_match_text(course.get("discipline", ""))
            full_norm = _normalize_match_text(course.get("full_name", ""))
            disc_ok = (
                not note_disc_norm
                or not disc_norm
                or disc_norm in note_disc_norm
                or note_disc_norm in disc_norm
                or note_disc_norm in full_norm
            )
            if not disc_ok:
                continue

            for a_item in (course.get("assign_items") or []):
                a_title_norm = _normalize_match_text(a_item.get("title", ""))
                if not a_title_norm:
                    continue
                if (
                    note_title_norm == a_title_norm
                    or (len(note_title_norm) > 10 and note_title_norm in a_title_norm)
                    or (len(a_title_norm) > 10 and a_title_norm in note_title_norm)
                ):
                    if a_item.get("is_submitted") or a_item.get("has_file"):
                        note["completed"] = True
                        note["has_attached_file"] = bool(a_item.get("has_file"))
                        note["lms_overdue"] = False
                        auto_completed += 1
                    else:
                        note["lms_overdue"] = bool(a_item.get("is_overdue"))
                    break

    # Шаг 2. Добавляем все остальные оценённые работы из актуальных курсов БРС,
    # которые не попали в окно экспорта .ics календаря СДО
    for course, cid, i_idx, disc_norm, full_norm, item_title_norm, item in graded_entries:
        if not course.get("is_current", True):
            continue
        if (cid, i_idx) in matched_entry_ids:
            continue

        title_raw = (item.get("title") or "").strip()
        title_low = title_raw.lower()
        # Пропускаем технические строки посещаемости, чтобы не смешивать их со сданными работами
        if "посещаемост" in title_low:
            continue

        synth_key = f"lms_brs_{cid}_{i_idx}"
        existing_synth = notes_dict.get(synth_key)
        notes_dict[synth_key] = {
            "text": title_raw,
            "description": existing_synth.get("description", "") if isinstance(existing_synth, dict) else "",
            "completed": True,
            "deadline": existing_synth.get("deadline", "") if isinstance(existing_synth, dict) else "",
            "deadline_time": existing_synth.get("deadline_time", "") if isinstance(existing_synth, dict) else "",
            "source": "lms",
            "lms_grade": item.get("grade_str", ""),
            "lms_range": item.get("range", "0-100"),
            "lms_feedback": item.get("feedback", ""),
            "lms_category": item.get("category", ""),
            "lms_item_type": item.get("item_type", ""),
            "lms_url": item.get("url", ""),
            "lesson": {
                "discipline": course.get("discipline") or "СДО РАНХиГС",
                "date": "",
                "num": "",
                "group": course.get("group") or "СДО",
                "teacher": course.get("teacher") or "",
                "room": "",
            },
        }
        auto_completed += 1

    return auto_completed


def parse_ics_deadlines(ics_text: str) -> dict[str, dict]:
    """
    Парсит содержимое .ics файла из Moodle и возвращает словарь заметок
    в формате NotesContext: { "lms_462814": { ... }, ... }
    """
    if not ics_text or "BEGIN:VCALENDAR" not in ics_text:
        return {}

    unfolded = re.sub(r"[\r\n]+[ \t]", "", ics_text)
    blocks = re.findall(r"BEGIN:VEVENT(.*?)END:VEVENT", unfolded, re.DOTALL)

    notes_dict: dict[str, dict] = {}

    for block in blocks:
        fields: dict[str, str] = {}
        for raw_line in block.strip().splitlines():
            line = raw_line.strip()
            if not line or ":" not in line:
                continue
            key_part, val = line.split(":", 1)
            key = key_part.split(";")[0].upper().strip()
            fields[key] = val.strip()

        uid = fields.get("UID", "")
        summary = fields.get("SUMMARY", "")
        description = fields.get("DESCRIPTION", "")
        categories = fields.get("CATEGORIES", "")
        dtstart = fields.get("DTSTART", "") or fields.get("DTEND", "")

        if not summary or not dtstart:
            continue

        clean_summary = _unescape_ics(summary)
        clean_summary = re.sub(r"\s*[-—–]\s*срок\s+сдачи\s*$", "", clean_summary, flags=re.IGNORECASE).strip()

        clean_desc = _unescape_ics(description)
        clean_desc = re.sub(r"\n*подробно здесь\s*$", "", clean_desc, flags=re.IGNORECASE).strip()

        clean_cat = _unescape_ics(categories)
        clean_cat = re.sub(r"\s*#\d+\s*$", "", clean_cat).strip()
        if not clean_cat:
            clean_cat = "СДО РАНХиГС"

        deadline_date = ""
        deadline_time = ""
        try:
            if dtstart.endswith("Z"):
                dt_utc = datetime.strptime(dtstart, "%Y%m%dT%H%M%SZ").replace(tzinfo=timezone.utc)
                dt_msk = dt_utc.astimezone(MSK)
            elif "T" in dtstart:
                dt_msk = datetime.strptime(dtstart[:15], "%Y%m%dT%H%M%S")
            else:
                dt_msk = datetime.strptime(dtstart[:8], "%Y%m%d")

            deadline_date = dt_msk.strftime("%Y-%m-%d")
            deadline_time = dt_msk.strftime("%H:%M")
        except Exception as e:
            logger.warning(f"[LMS Parser] Не удалось распарсить дату '{dtstart}': {e}")
            continue

        uid_clean = uid.split("@")[0] if "@" in uid else re.sub(r"[^a-zA-Z0-9_-]", "", uid)
        if not uid_clean:
            continue
        note_key = f"lms_{uid_clean}"

        notes_dict[note_key] = {
            "text": clean_summary,
            "description": clean_desc,
            "completed": False,
            "deadline": deadline_date,
            "deadline_time": deadline_time,
            "source": "lms",
            "lesson": {
                "discipline": clean_cat,
                "date": "",
                "num": "",
                "group": "СДО",
                "teacher": "",
                "room": "",
            },
        }

    return notes_dict


async def fetch_and_parse_lms_calendar(raw_url: str, timeout: float = 15.0) -> tuple[str, dict[str, dict]]:
    """
    Нормализует ссылку, скачивает .ics с lms.ranepa.ru и возвращает (normalized_url, notes_dict).
    """
    normalized_url = normalize_lms_calendar_url(raw_url)
    ics_text = await asyncio.to_thread(_download_ics, normalized_url, timeout)
    notes_dict = parse_ics_deadlines(ics_text)
    return normalized_url, notes_dict


def _sync_brs_via_credentials_blocking(username: str, password: str, timeout: float = 15.0) -> dict:
    """
    Выполняет одноразовый вход в lms.ranepa.ru:
    1. Авторизуется и получает sesskey.
    2. Автоматически получает ссылку экспорта календаря (export_execute.php).
    3. Выгружает сводную таблицу БРС (/grade/report/overview/index.php).
    4. Выгружает детальные оценки по текущим предметам (/course/user.php?mode=grade).
    5. Сразу выполняет выход (logout.php), уничтожая сессию.
    """
    cj = http.cookiejar.CookieJar()
    opener = urllib.request.build_opener(
        urllib.request.HTTPCookieProcessor(cj),
        urllib.request.HTTPSHandler(context=_ssl_ctx),
    )
    opener.addheaders = [
        ("User-Agent", DEFAULT_HEADERS["User-Agent"]),
        ("Referer", "https://lms.ranepa.ru/login/index.php"),
    ]

    # 1. Получаем logintoken
    r_login_page = opener.open("https://lms.ranepa.ru/login/index.php", timeout=timeout)
    login_page_html = r_login_page.read().decode("utf-8", errors="replace")
    token_m = re.search(r'name="logintoken"\s+value="([^"]+)"', login_page_html)
    logintoken = token_m.group(1) if token_m else ""

    # 2. Отправляем форму входа
    login_data = urllib.parse.urlencode({
        "username": username.strip(),
        "password": password,
        "logintoken": logintoken,
    }).encode("utf-8")

    r_auth = opener.open("https://lms.ranepa.ru/login/index.php", data=login_data, timeout=timeout)
    auth_html = r_auth.read().decode("utf-8", errors="replace")
    final_url = r_auth.geturl()

    if "/login/index.php" in final_url or "loginerrors" in auth_html:
        raise ValueError("Неверный логин или пароль от СДО РАНХиГС")

    sess_m = re.search(r'"sesskey"\s*:\s*"([^"]+)"', auth_html)
    sesskey = sess_m.group(1) if sess_m else ""

    calendar_url = ""
    try:
        # 3. Автоматически получаем ссылку на экспорт календаря
        if sesskey:
            cal_form = urllib.parse.urlencode({
                "sesskey": sesskey,
                "_qf__core_calendar_export_form": "1",
                "events[exportevents]": "all",
                "period[timeperiod]": "recentupcoming",
                "generateurl": "1",
            }).encode("utf-8")
            req_cal = urllib.request.Request(
                "https://lms.ranepa.ru/calendar/export.php?",
                data=cal_form,
                headers={
                    "User-Agent": DEFAULT_HEADERS["User-Agent"],
                    "Referer": "https://lms.ranepa.ru/calendar/export.php?",
                },
            )
            r_cal = opener.open(req_cal, timeout=timeout)
            cal_html = r_cal.read().decode("utf-8", errors="replace")
            url_m = re.search(r"https://lms\.ranepa\.ru/calendar/export_execute\.php\?[^\"<>\s]+", cal_html)
            if url_m:
                calendar_url = normalize_lms_calendar_url(url_m.group(0))
    except Exception as e:
        logger.warning(f"[LMS BRS] Не удалось автоматически получить ссылку календаря: {e}")

    # 4. Загружаем обзор оценок БРС
    r_ov = opener.open("https://lms.ranepa.ru/grade/report/overview/index.php", timeout=timeout)
    ov_html = r_ov.read().decode("utf-8", errors="replace")
    user_id, courses = parse_overview_html(ov_html)

    active_group = _SelectActiveGroup(courses)
    for c in courses:
        c["is_current"] = bool(active_group and c.get("group") == active_group) or not active_group

    # 5. Загружаем детальную таблицу БРС для всех неархивных курсов (в первую очередь актуальных)
    target_courses = [
        c for c in courses
        if c.get("course_id") and "(архив)" not in (c.get("full_name") or "").lower()
    ][:24]

    cookie_header = "; ".join(f"{cookie.name}={cookie.value}" for cookie in cj)

    def _fetch_one_course(c_obj: dict):
        cid = c_obj["course_id"]
        uid_param = f"&user={user_id}" if user_id else ""
        url = f"https://lms.ranepa.ru/course/user.php?mode=grade&id={cid}{uid_param}"
        req = urllib.request.Request(
            url,
            headers={
                "User-Agent": DEFAULT_HEADERS["User-Agent"],
                "Cookie": cookie_header,
                "Referer": "https://lms.ranepa.ru/grade/report/overview/index.php",
            },
        )
        try:
            with urllib.request.urlopen(req, context=_ssl_ctx, timeout=timeout) as resp:
                c_html = resp.read().decode("utf-8", errors="replace")
            details = parse_course_gradebook_html(c_html)
            c_obj["tku_score"] = details["tku_score"]
            c_obj["db_score"] = details["db_score"]
            c_obj["pa_score"] = details["pa_score"]
            if details["total_score"] is not None:
                c_obj["total_score"] = details["total_score"]
                c_obj["total_score_str"] = details["total_score_str"]
                c_obj["rating"] = classify_brs_rating(details["total_score"])
            c_obj["items"] = details["items"]
            # Также загружаем список всех заданий курса со статусом сдачи и просрочки
            try:
                req_assign = urllib.request.Request(
                    f"https://lms.ranepa.ru/mod/assign/index.php?id={cid}",
                    headers={
                        "User-Agent": DEFAULT_HEADERS["User-Agent"],
                        "Cookie": cookie_header,
                        "Referer": "https://lms.ranepa.ru/grade/report/overview/index.php",
                    },
                )
                with urllib.request.urlopen(req_assign, context=_ssl_ctx, timeout=timeout) as resp_assign:
                    assign_html = resp_assign.read().decode("utf-8", errors="replace")
                c_obj["assign_items"] = parse_course_assign_index_html(assign_html)
            except Exception:
                pass
        except Exception as e:
            logger.warning(f"[LMS BRS] Ошибка загрузки курса {cid}: {e}")

    if target_courses:
        with ThreadPoolExecutor(max_workers=6) as pool:
            list(pool.map(_fetch_one_course, target_courses))

    # 6. Мгновенно уничтожаем сессию на сервере СДО (Logout)
    try:
        if sesskey:
            opener.open(f"https://lms.ranepa.ru/login/logout.php?sesskey={sesskey}", timeout=5.0)
    except Exception:
        pass
    cj.clear()

    return {
        "user_id": user_id,
        "student_group": active_group,
        "calendar_url": calendar_url,
        "courses": courses,
    }


async def fetch_lms_brs_and_calendar(
    username: str,
    password: str,
    existing_cal_url: str = "",
    eljur_attendance: Optional[dict] = None,
    custom_curriculum: Optional[dict] = None,
    curriculum_plan_id: Optional[str] = None,
) -> dict:
    """
    Асинхронная обертка: логинится в СДО без сохранения пароля, забирает БРС + ссылку календаря,
    выгружает дедлайны из календаря и автоматически помечает оцененные в БРС задания как сданные.
    """
    if not username or not password:
        raise ValueError("Введите логин и пароль от СДО РАНХиГС")

    raw_res = await asyncio.to_thread(_sync_brs_via_credentials_blocking, username, password)
    cal_url = raw_res.get("calendar_url") or existing_cal_url or ""

    lms_notes: dict[str, dict] = {}
    if cal_url:
        try:
            cal_url, lms_notes = await fetch_and_parse_lms_calendar(cal_url)
        except Exception as e:
            logger.warning(f"[LMS BRS] Ошибка синхронизации календаря при выгрузке БРС: {e}")

    courses = raw_res.get("courses") or []
    curriculum_info = apply_attendance_and_curriculum_to_courses(
        courses, eljur_attendance, custom_curriculum, curriculum_plan_id
    )
    auto_completed = apply_brs_grades_to_notes(lms_notes, courses)

    msk_now = datetime.now(MSK).strftime("%d.%m.%Y %H:%M")

    return {
        "calendar_url": cal_url,
        "lms_notes": lms_notes,
        "auto_completed_count": auto_completed,
        "updated_at": msk_now,
        "brs_data": {
            "updated_at": msk_now,
            "student_group": raw_res.get("student_group") or "",
            "courses": courses,
            "eljur_attendance": eljur_attendance,
            "curriculum": curriculum_info,
        },
    }


async def process_extension_brs_sync(
    payload: dict,
    existing_cal_url: str = "",
    eljur_attendance: Optional[dict] = None,
    custom_curriculum: Optional[dict] = None,
    curriculum_plan_id: Optional[str] = None,
) -> dict:
    """
    Обрабатывает данные БРС и календаря, присланные напрямую из браузера студента
    расширением ranepa-moodle-theme или закладкой-скриптом (по 6-значному коду без передачи пароля).
    Поддерживает как передачу сырого HTML (overview_html + course_htmls/courses_html), так и готового списка courses.
    """
    ov_html = payload.get("overview_html") or ""
    course_htmls = payload.get("course_htmls") or payload.get("courses_html") or {}
    assign_htmls = payload.get("assign_htmls") or payload.get("assigns_html") or {}
    raw_cal_url = (
        payload.get("calendar_url")
        or payload.get("calendar_export_url")
        or existing_cal_url
        or ""
    )

    if ov_html:
        _, courses = parse_overview_html(ov_html)
    else:
        courses = payload.get("courses") or []

    active_group = _SelectActiveGroup(courses)
    for c in courses:
        c["is_current"] = bool(active_group and c.get("group") == active_group) or not active_group
        cid = str(c.get("course_id") or "")
        if cid and cid in course_htmls:
            details = parse_course_gradebook_html(course_htmls[cid])
            c["tku_score"] = details["tku_score"]
            c["db_score"] = details["db_score"]
            c["pa_score"] = details["pa_score"]
            if details["total_score"] is not None:
                c["total_score"] = details["total_score"]
                c["total_score_str"] = details["total_score_str"]
                c["rating"] = classify_brs_rating(details["total_score"])
            c["items"] = details["items"]
            if cid in assign_htmls:
                c["assign_items"] = parse_course_assign_index_html(assign_htmls[cid])
        elif "rating" not in c:
            c["rating"] = classify_brs_rating(_parse_float_score(str(c.get("total_score_str") or c.get("total_score") or "")))

    curriculum_info = apply_attendance_and_curriculum_to_courses(
        courses, eljur_attendance, custom_curriculum, curriculum_plan_id
    )

    cal_url = ""
    lms_notes: dict[str, dict] = {}
    if raw_cal_url:
        try:
            cal_url, lms_notes = await fetch_and_parse_lms_calendar(raw_cal_url)
        except Exception as e:
            logger.warning(f"[Extension BRS] Ошибка парсинга календаря: {e}")

    auto_completed = apply_brs_grades_to_notes(lms_notes, courses)
    msk_now = datetime.now(MSK).strftime("%d.%m.%Y %H:%M")

    return {
        "calendar_url": cal_url,
        "lms_notes": lms_notes,
        "auto_completed_count": auto_completed,
        "updated_at": msk_now,
        "brs_data": {
            "updated_at": msk_now,
            "student_group": active_group,
            "courses": courses,
            "eljur_attendance": eljur_attendance,
            "curriculum": curriculum_info,
        },
    }

import pdfplumber
from collections import defaultdict
from dataclasses import dataclass, asdict
from typing import List, Tuple, Optional, Dict, Any
import colorsys
import os
from datetime import datetime
import argparse
import json
import re


@dataclass
class AccessibilityIssue:
    """Класс для хранения информации о проблемах доступности"""
    page: int
    x: float
    y: float
    text: str
    issue_type: str
    description: str
    severity: str  # 'low', 'medium', 'high'
    font_name: str = ""
    font_size: float = 0.0
    color: Tuple[float, float, float] = (0, 0, 0)  # RGB
    background_color: Tuple[float, float, float] = (1, 1, 1)  # RGB


class EnhancedPDFAccessibilityAnalyzer:
    """Улучшенный анализатор доступности PDF с расширенными проверками"""

    # Минимальные требования WCAG 2.1
    MIN_FONT_SIZE = 12  # минимальный размер шрифта для основного текста
    MIN_HEADING_SIZE = 14  # минимальный размер для заголовков

    # Контрастность (WCAG AA уровень)
    MIN_CONTRAST_RATIO = 4.5  # для обычного текста
    MIN_CONTRAST_LARGE = 3.0  # для крупного текста (18pt+ или 14pt жирный)

    # Хорошо читаемые шрифты для слабовидящих
    ACCESSIBLE_FONTS = {
        'Arial', 'Helvetica', 'Verdana', 'Tahoma', 'Calibri',
        'Georgia', 'Times New Roman', 'Lucida Sans', 'Trebuchet MS',
        'Open Sans', 'Roboto', 'Lato', 'Montserrat',
        'LiberationSans', 'LiberationSerif', 'DejaVu Sans', 'DejaVu Serif'
    }

    # Плохо читаемые шрифты (декоративные, моноширинные и т.д.)
    POOR_READABILITY_FONTS = {
        'Comic Sans', 'Papyrus', 'Brush Script', 'Jokerman',
        'Chiller', 'Curly', 'Old English', 'Gothic',
        'Courier', 'Consolas', 'Monaco', 'Menlo', 'Source Code Pro'
    }

    def __init__(self, pdf_path: str):
        self.pdf_path = pdf_path
        self.issues: List[AccessibilityIssue] = []
        self.color_issues: List[dict] = []  # Специальный список проблем с цветами
        self.line_cache = {}  # Кэш для строк текста
        self.problematic_colors_found = []  # Для отладки
        self.full_text_cache = {}  # Кэш для полного текста строк
        self.screenshots_dir = "accessibility_screenshots"

    def normalize_color(self, color) -> Tuple[float, float, float]:
        """Нормализует цвет в формат RGB (0-1)"""
        try:
            if isinstance(color, (int, float)):
                # Монохромный цвет (grayscale)
                return (float(color), float(color), float(color))
            elif isinstance(color, tuple) or isinstance(color, list):
                if len(color) == 1:
                    # Монохромный
                    return (float(color[0]), float(color[0]), float(color[0]))
                elif len(color) == 3:
                    # RGB
                    return (float(color[0]), float(color[1]), float(color[2]))
                elif len(color) == 4:
                    # CMYK - конвертируем в RGB (упрощенно)
                    c, m, y, k = color
                    r = (1 - c) * (1 - k)
                    g = (1 - m) * (1 - k)
                    b = (1 - y) * (1 - k)
                    return (r, g, b)
            elif color is None:
                # Цвет не указан - предполагаем черный
                return (0.0, 0.0, 0.0)
        except Exception as e:
            print(f"⚠️ Ошибка нормализации цвета {color}: {e}")

        # По умолчанию черный
        return (0.0, 0.0, 0.0)

    def is_large_text_by_wcag(self, font_size: float, font_name: str) -> bool:
        """
        Определяет, является ли текст крупным по WCAG 2.1
        Возвращает True если:
        - Размер ≥ 18pt
        ИЛИ
        - Размер ≥ 14pt И текст жирный
        """
        try:
            # Проверяем, является ли шрифт жирным
            is_bold = any(bold_term in font_name for bold_term in
                          ['Bold', 'BoldItalic', 'Black', 'Heavy', '-Bold', 'bold'])

            # Критерии WCAG
            if font_size >= 18:
                return True  # ≥18pt - всегда крупный
            elif font_size >= 14 and is_bold:
                return True  # ≥14pt И жирный - крупный
            else:
                return False  # не соответствует критериям
        except:
            return False

    def calculate_luminance(self, color: Tuple[float, float, float]) -> float:
        """Рассчитывает относительную яркость цвета (0-1)"""
        try:
            r, g, b = color

            # Преобразование sRGB в линейные значения
            def srgb_to_linear(channel):
                if channel <= 0.03928:
                    return channel / 12.92
                return ((channel + 0.055) / 1.055) ** 2.4

            r_linear = srgb_to_linear(r)
            g_linear = srgb_to_linear(g)
            b_linear = srgb_to_linear(b)

            # Рассчет относительной яркости
            return 0.2126 * r_linear + 0.7152 * g_linear + 0.0722 * b_linear
        except:
            return 0.0

    def calculate_contrast_ratio(self, color1: Tuple[float, float, float],
                                 color2: Tuple[float, float, float]) -> float:
        """Рассчитывает контрастность между двумя цветами"""
        try:
            l1 = self.calculate_luminance(color1)
            l2 = self.calculate_luminance(color2)

            # Более светлый и темный цвета
            lighter = max(l1, l2)
            darker = min(l1, l2)

            return (lighter + 0.05) / (darker + 0.05)
        except:
            return 1.0  # Минимальная контрастность при ошибке

    def rgb_to_hsv(self, color: Tuple[float, float, float]) -> Tuple[float, float, float]:
        """Конвертирует RGB в HSV цветовое пространство"""
        try:
            return colorsys.rgb_to_hsv(color[0], color[1], color[2])
        except:
            return (0.0, 0.0, 0.0)

    def identify_problematic_color(self, color: Tuple[float, float, float]) -> Optional[str]:
        """Определяет, является ли цвет проблемным для доступности"""
        try:
            # Конвертируем в HSV для лучшей идентификации
            h, s, v = self.rgb_to_hsv(color)

            # Определяем цвет по Hue
            if 0.2 <= h <= 0.4:  # Зеленый диапазон
                if s > 0.3 and v > 0.4:
                    if v > 0.7:
                        return "светло-зеленый"
                    else:
                        return "зеленый"
            elif h <= 0.05 or h >= 0.95:  # Красный диапазон
                if s > 0.3 and v > 0.4:
                    if v > 0.7:
                        return "светло-красный"
                    else:
                        return "красный"
            elif 0.55 <= h <= 0.75:  # Синий диапазон
                if s > 0.3 and v > 0.4:
                    if v > 0.7:
                        return "светло-синий"
                    else:
                        return "синий"
            elif 0.05 <= h <= 0.15:  # Желтый/оранжевый
                if s > 0.3 and v > 0.6:
                    return "желтый" if v > 0.8 else "оранжевый"

            # Проверяем серые оттенки
            if s < 0.1 and 0.3 <= v <= 0.7:
                return "серый"

            return None
        except:
            return None

    def normalize_font_name(self, font_name: str) -> str:
        """Нормализует название шрифта для сравнения"""
        try:
            if '+' in font_name:
                font_name = font_name.split('+')[-1]

            font_name = font_name.replace('-Bold', '').replace('-Italic', '')
            font_name = font_name.replace('Bold', '').replace('Italic', '')
            font_name = font_name.replace('MT', '').replace('PS', '')

            return font_name.strip()
        except:
            return font_name

    def check_font_readability(self, font_name: str) -> Tuple[bool, str]:
        """Проверяет, относится ли шрифт к хорошо читаемым"""
        try:
            normalized_name = self.normalize_font_name(font_name)

            for accessible_font in self.ACCESSIBLE_FONTS:
                if accessible_font.lower() in normalized_name.lower():
                    return True, f"Хорошо читаемый шрифт: {accessible_font}"

            for poor_font in self.POOR_READABILITY_FONTS:
                if poor_font.lower() in normalized_name.lower():
                    return False, f"Плохо читаемый шрифт: {poor_font}"

            return False, f"Неизвестный шрифт: {normalized_name}"
        except:
            return True, "Не удалось определить шрифт"

    def extract_background_color(self, page, x: float, y: float) -> Tuple[float, float, float]:
        """Упрощенная версия определения цвета фона"""
        return (1.0, 1.0, 1.0)  # белый фон

    def remove_duplicate_chars(self, text: str) -> str:
        """Удаляет дублированные символы из текста"""
        if not text or len(text) < 2:
            return text

        # Паттерн для поиска дублированных символов (2 или более подряд)

        # Удаляем последовательные дубликаты
        result = []
        i = 0
        while i < len(text):
            result.append(text[i])
            # Пропускаем следующие одинаковые символы
            j = i + 1
            while j < len(text) and text[j] == text[i]:
                j += 1
            i = j

        cleaned = ''.join(result)

        # Также убираем дубли через каждые 2 символа
        # (типа "ГЛООССААРРИИЙЙ")
        # Это может быть связано с кернингом/наложением в PDF
        if len(cleaned) % 2 == 0:
            # Проверяем, нет ли паттерна дублирования через символ
            half = len(cleaned) // 2
            first_half = cleaned[:half]
            second_half = cleaned[half:]

            # Если вторая половина похожа на первую с пропусками
            if first_half == second_half:
                # Берем каждый второй символ из первой половины
                return first_half

        return cleaned

    def count_words(self, text: str) -> int:
        """Подсчитывает количество слов в тексте"""
        if not text or not text.strip():
            return 0
        
        # Нормализуем текст - убираем дубли
        normalized = self.remove_duplicate_chars(text.strip())
        if not normalized:
            return 0
        
        # Разбиваем на слова (разделители: пробелы, знаки препинания)
        # Используем регулярное выражение для более точного подсчета
        words = re.findall(r'\b\w+\b', normalized, re.UNICODE)
        return len(words)

    def normalize_text_for_grouping(self, text: str) -> str:
        """Нормализует текст для группировки"""
        if not text:
            return text

        # 1. Удаляем дублированные символы
        text = self.remove_duplicate_chars(text)

        # 2. Удаляем лишние пробелы и приводим к нижнему регистру
        text = ' '.join(text.split()).lower()

        # 3. Удаляем знаки препинания в конце для лучшей группировки
        text = text.rstrip('.,;:!?')

        return text

    def get_text_line(self, page, y_position: float, tolerance: float = 2.0) -> Tuple[List[dict], str]:
        """Получает все символы в строке по Y-координате и полный текст строки"""
        try:
            cache_key = (id(page), round(y_position, 2))

            if cache_key not in self.line_cache:
                line_chars = []
                for char in page.chars:
                    if abs(char['y0'] - y_position) < tolerance:
                        line_chars.append(char)

                # Сортируем по X координате
                line_chars.sort(key=lambda c: c['x0'])

                # Получаем полный текст строки
                line_text = ''.join([c.get('text', '') for c in line_chars])

                self.line_cache[cache_key] = (line_chars, line_text)
                self.full_text_cache[cache_key] = line_text

            return self.line_cache[cache_key]
        except:
            return ([], "")

    def analyze_text_line_contrast(self, page_num: int, line_chars: List[dict], line_text: str) -> List[
        AccessibilityIssue]:
        """Анализирует контрастность целой строки текста"""
        issues = []

        if not line_chars or not line_text.strip():
            return issues

        try:
            # Нормализуем текст - убираем дубли
            normalized_line_text = self.remove_duplicate_chars(line_text.strip())
            if not normalized_line_text or len(normalized_line_text) < 3:
                return issues

            # Получаем средние параметры строки
            avg_size = sum(char.get('size', 12) for char in line_chars) / len(line_chars)
            is_bold = any('Bold' in char.get('fontname', '') for char in line_chars)
            is_large_wcag = self.is_large_text_by_wcag(avg_size, line_chars[0].get('fontname', ''))

            # Определяем требуемую контрастность
            required_contrast = self.MIN_CONTRAST_LARGE if is_large_wcag else self.MIN_CONTRAST_RATIO

            # Анализируем каждый символ
            for char in line_chars:
                try:
                    raw_color = char.get('non_stroking_color', (0, 0, 0))
                    text_color = self.normalize_color(raw_color)

                    # Для отладки - сохраняем найденные цвета
                    if raw_color not in [(0, 0, 0), 0, None, (0,), [0]]:
                        self.problematic_colors_found.append({
                            'page': page_num,
                            'color': raw_color,
                            'normalized': text_color,
                            'text': char.get('text', '')
                        })

                    bg_color = self.extract_background_color(None, char.get('x0', 0), char.get('y0', 0))
                    contrast_ratio = self.calculate_contrast_ratio(text_color, bg_color)

                    if contrast_ratio < required_contrast:
                        # Определяем проблемный цвет
                        color_name = self.identify_problematic_color(text_color)

                        # Определяем серьезность
                        if contrast_ratio < 2.0:
                            severity = 'high'
                        elif contrast_ratio < 3.0:
                            severity = 'medium'
                        else:
                            severity = 'low'

                        # Улучшенное описание проблемы
                        if is_large_wcag:
                            size_info = f"Крупный текст ({avg_size:.1f}pt{' жирный' if is_bold else ''})"
                            contrast_req = f"требуется ≥3.0:1"
                        else:
                            size_info = f"Обычный текст ({avg_size:.1f}pt)"
                            contrast_req = f"требуется ≥4.5:1"

                        issue_desc = f"{size_info}. Контрастность: {contrast_ratio:.1f}:1 ({contrast_req})"
                        if color_name:
                            issue_desc += f". Проблемный цвет: {color_name}"

                        # Получаем больше текста для примера (нормализованного)
                        text_preview = normalized_line_text
                        if len(text_preview) > 150:
                            text_preview = text_preview[:147] + "..."

                        issues.append(AccessibilityIssue(
                            page=page_num,
                            x=char.get('x0', 0),
                            y=char.get('y0', 0),
                            text=text_preview,
                            issue_type='Контрастность',
                            description=issue_desc,
                            severity=severity,
                            font_name=char.get('fontname', ''),
                            font_size=char.get('size', 12),
                            color=text_color,
                            background_color=bg_color
                        ))

                        # Добавляем в отдельный список проблемных цветов (с нормализованным текстом)
                        if color_name and contrast_ratio < 4.5:
                            self.color_issues.append({
                                'page': page_num,
                                'raw_color': raw_color,
                                'color': text_color,
                                'color_name': color_name,
                                'contrast': contrast_ratio,
                                'required': required_contrast,
                                'text_sample': normalized_line_text[:100].strip(),
                                'full_text': normalized_line_text.strip(),
                                'position': (char.get('x0', 0), char.get('y0', 0)),
                                'is_large': is_large_wcag,
                                'font_size': char.get('size', 12)
                            })
                except Exception:
                    continue  # Пропускаем проблемные символы

        except Exception:
            pass  # Пропускаем проблемные строки

        return issues

    def analyze_page(self, page_num: int, page) -> List[AccessibilityIssue]:
        """Анализирует одну страницу на проблемы доступности"""
        page_issues = []
        processed_lines = set()

        try:
            # Проходим по всем символам
            for char in page.chars:
                try:
                    # Пропускаем пробелы и непечатаемые символы
                    char_text = char.get('text', '')
                    if char_text.isspace() or not char_text.strip():
                        continue

                    # Получаем строку, если еще не обрабатывали
                    line_y = round(char.get('y0', 0), 2)
                    if line_y not in processed_lines:
                        line_chars, line_text = self.get_text_line(page, char.get('y0', 0))

                        # Анализируем контрастность строки (только если есть текст)
                        if line_text.strip():
                            contrast_issues = self.analyze_text_line_contrast(page_num, line_chars, line_text)
                            page_issues.extend(contrast_issues)

                        processed_lines.add(line_y)

                    # 2. ПРОВЕРКА РАЗМЕРА ШРИФТА (индивидуальная)
                    font_size = char.get('size', 12)
                    font_name = char.get('fontname', '')
                    is_bold = 'Bold' in font_name
                    is_large_wcag = self.is_large_text_by_wcag(font_size, font_name)

                    # Получаем строку для текста
                    line_chars, line_text = self.get_text_line(page, char.get('y0', 0))
                    normalized_text = self.remove_duplicate_chars(line_text.strip())

                    if not normalized_text or len(normalized_text) < 3:
                        continue

                    # Определяем тип текста
                    if is_bold and font_size >= 14:
                        # Заголовок
                        if font_size < self.MIN_HEADING_SIZE:
                            text_preview = normalized_text[:80] + ("..." if len(normalized_text) > 80 else "")

                            page_issues.append(AccessibilityIssue(
                                page=page_num,
                                x=char.get('x0', 0),
                                y=char.get('y0', 0),
                                text=text_preview,
                                issue_type='Размер шрифта',
                                description=f'Размер заголовка {font_size:.1f}pt меньше минимального {self.MIN_HEADING_SIZE}pt',
                                severity='high',
                                font_name=font_name,
                                font_size=font_size
                            ))
                    elif not is_large_wcag:  # Обычный текст (не крупный по WCAG)
                        if font_size < self.MIN_FONT_SIZE:
                            text_preview = normalized_text[:80] + ("..." if len(normalized_text) > 80 else "")

                            page_issues.append(AccessibilityIssue(
                                page=page_num,
                                x=char.get('x0', 0),
                                y=char.get('y0', 0),
                                text=text_preview,
                                issue_type='Размер шрифта',
                                description=f'Размер текста {font_size:.1f}pt меньше минимального {self.MIN_FONT_SIZE}pt',
                                severity='medium' if font_size >= 10 else 'high',
                                font_name=font_name,
                                font_size=font_size
                            ))

                    # 3. ПРОВЕРКА ЧИТАЕМОСТИ ШРИФТА
                    is_readable, readability_info = self.check_font_readability(font_name)

                    if not is_readable:
                        text_preview = normalized_text[:80] + ("..." if len(normalized_text) > 80 else "")

                        page_issues.append(AccessibilityIssue(
                            page=page_num,
                            x=char.get('x0', 0),
                            y=char.get('y0', 0),
                            text=text_preview,
                            issue_type='Читаемость шрифта',
                            description=readability_info,
                            severity='medium',
                            font_name=font_name,
                            font_size=font_size
                        ))
                except:
                    continue  # Пропускаем проблемные символы

        except Exception as e:
            print(f"⚠️ Ошибка при анализе страницы {page_num}: {e}")

        return page_issues

    def group_and_summarize_issues_improved(self) -> Dict[str, Any]:
        """Группирует и агрегирует проблемы с четким разделением по серьезности"""

        summary = {
            'by_type_severity': defaultdict(lambda: {
                'high': {'places': 0, 'words': 0},
                'medium': {'places': 0, 'words': 0},
                'low': {'places': 0, 'words': 0}
            }),
            'by_type': defaultdict(lambda: {
                'total_places': 0,
                'total_words': 0,
                'pages_affected': set()
            }),
            'by_severity': defaultdict(lambda: {
                'places': 0,
                'words': 0,
                'types': defaultdict(lambda: {'places': 0, 'words': 0})
            }),
            'overall': {
                'total_places': 0,
                'total_words': 0,
                'pages_with_issues': set(),
                'types_distribution': defaultdict(int),
                'severity_distribution': defaultdict(int)
            }
        }

        # Проходим по всем проблемам
        for issue in self.issues:
            # Подсчитываем слова в тексте проблемы
            word_count = self.count_words(issue.text)
            
            # 1. Группировка по типу + серьезность (вложенная)
            type_sev_group = summary['by_type_severity'][issue.issue_type]
            type_sev_group[issue.severity]['places'] += 1
            type_sev_group[issue.severity]['words'] += word_count

            # 2. Группировка по типу (суммарно)
            type_group = summary['by_type'][issue.issue_type]
            type_group['total_places'] += 1
            type_group['total_words'] += word_count
            type_group['pages_affected'].add(issue.page)

            # 3. Группировка по серьезности
            severity_group = summary['by_severity'][issue.severity]
            severity_group['places'] += 1
            severity_group['words'] += word_count
            severity_group['types'][issue.issue_type]['places'] += 1
            severity_group['types'][issue.issue_type]['words'] += word_count

            # 4. Общая статистика
            summary['overall']['total_places'] += 1
            summary['overall']['total_words'] += word_count
            summary['overall']['pages_with_issues'].add(issue.page)
            summary['overall']['types_distribution'][issue.issue_type] += 1
            summary['overall']['severity_distribution'][issue.severity] += 1

        return summary

    def create_screenshot(self, page_num: int, bbox: Tuple[float, float, float, float] = None,
                          issue_type: str = None, output_dir: str = None,
                          full_page: bool = False, highlight_issue: bool = False,
                          issue_position: Tuple[float, float] = None) -> Optional[str]:
        """
        Создает скриншот страницы или области

        Args:
            page_num: номер страницы
            bbox: bounding box (x0, y0, x1, y1) для частичного скриншота
            issue_type: тип проблемы
            output_dir: директория для сохранения
            full_page: если True, создает скриншот всей страницы
            highlight_issue: если True, выделяет проблемную область
            issue_position: позиция проблемы (x, y) для выделения

        Returns:
            Путь к сохраненному скриншоту или None
        """
        try:
            if output_dir is None:
                output_dir = self.screenshots_dir

            # Создаем директорию, если не существует
            os.makedirs(output_dir, exist_ok=True)

            with pdfplumber.open(self.pdf_path) as pdf:
                if page_num > len(pdf.pages):
                    return None

                page = pdf.pages[page_num - 1]

                if full_page:
                    # Создаем скриншот всей страницы
                    im = page.to_image(resolution=150)
                    screenshot_type = "full_page"
                else:
                    if bbox is None:
                        # Если bbox не указан, используем всю страницу
                        bbox = (0, 0, page.width, page.height)
                        screenshot_type = "full_page"
                    else:
                        # Добавляем отступы вокруг проблемной области
                        padding = 50 if highlight_issue else 20
                        x0, y0, x1, y1 = bbox
                        x0 = max(0, x0 - padding)
                        y0 = max(0, y0 - padding)
                        x1 = min(page.width, x1 + padding)
                        y1 = min(page.height, y1 + padding)

                        # Вырезаем область
                        cropped_page = page.crop((x0, y0, x1, y1))
                        im = cropped_page.to_image(resolution=150)
                        screenshot_type = "area"

                # Если нужно выделить проблемную область
                if highlight_issue and issue_position:
                    try:
                        # Конвертируем координаты для выделения
                        if not full_page:
                            # Для частичного скриншота
                            x, y = issue_position
                            rel_x = x - bbox[0] if bbox else x
                            rel_y = y - bbox[1] if bbox else y

                            # Добавляем выделение (красный прямоугольник)
                            im.draw_rect((rel_x - 10, rel_y - 5, rel_x + 100, rel_y + 10),
                                         fill=None, stroke="red", stroke_width=3)

                            # Добавляем текст с типом проблемы
                            if issue_type:
                                im.draw_text((rel_x, rel_y - 20), issue_type,
                                             fill="red", font_size=12)
                    except Exception as e:
                        print(f"⚠️ Ошибка при выделении проблемы: {e}")

                # Генерируем имя файла
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                if issue_type:
                    filename = f"page_{page_num}_{issue_type}_{screenshot_type}_{timestamp}.png"
                else:
                    filename = f"page_{page_num}_{screenshot_type}_{timestamp}.png"
                filepath = os.path.join(output_dir, filename)

                # Сохраняем изображение
                im.save(filepath, format="PNG", quality=95)

                print(f"📸 Скриншот сохранен: {filepath}")
                return filepath

        except Exception as e:
            print(f"⚠️ Ошибка при создании скриншота: {e}")
            return None

    def create_full_page_screenshots(self, pages: List[int] = None, output_dir: str = None) -> Dict[int, str]:
        """
        Создает полностаничные скриншоты для указанных страниц

        Args:
            pages: список номеров страниц (если None, создает для всех страниц с проблемами)
            output_dir: директория для сохранения

        Returns:
            Словарь с номерами страниц и путями к скриншотам
        """
        screenshots = {}

        if output_dir is None:
            output_dir = os.path.join(self.screenshots_dir, "full_pages")

        # Определяем, для каких страниц делать скриншоты
        if pages is None:
            # Создаем скриншоты для всех страниц с проблемами
            pages_with_issues = set(issue.page for issue in self.issues)
            pages = sorted(pages_with_issues)

        print(f"\n📸 Создание полностаничных скриншотов для {len(pages)} страниц...")

        for page_num in pages:
            print(f"  Страница {page_num}...", end='\r')

            screenshot_path = self.create_screenshot(
                page_num=page_num,
                full_page=True,
                output_dir=output_dir
            )

            if screenshot_path:
                screenshots[page_num] = screenshot_path

        print(f"\n✅ Создано {len(screenshots)} полностаничных скриншотов")
        return screenshots

    def truncate_text_smart(self, text: str, max_length: int = 50) -> str:
        """Умное обрезание текста по границе слова"""
        if len(text) <= max_length:
            return text

        # Ищем последний пробел перед максимальной длиной
        truncated = text[:max_length]
        last_space = truncated.rfind(' ')

        if last_space > max_length * 0.7:  # Если пробел есть в последней трети
            return truncated[:last_space] + "..."
        else:
            return truncated + "..."

    def group_issues_by_text_and_page(self, issues: List[AccessibilityIssue]) -> Dict[str, Dict[str, Any]]:
        """
        Группирует проблемы по нормализованному тексту и страницам
        Возвращает: {текст: {страницы: {страница: [проблемы]}, count: X, first_issue: проблема}}
        """
        text_groups = defaultdict(lambda: {
            'pages': defaultdict(list),
            'total_count': 0,
            'first_issue': None,
            'issue_types': set(),
            'descriptions': set()
        })

        for issue in issues:
            # Нормализуем текст (убираем дубли и приводим к нижнему регистру)
            normalized_text = self.normalize_text_for_grouping(issue.text)

            if len(normalized_text) < 3:  # Пропускаем слишком короткие тексты
                continue

            group = text_groups[normalized_text]
            group['pages'][issue.page].append(issue)
            group['total_count'] += 1
            group['issue_types'].add(issue.issue_type)
            group['descriptions'].add(issue.description)

            # Сохраняем первый экземпляр для отчета
            if group['first_issue'] is None:
                group['first_issue'] = issue

        return text_groups

    def group_issues_by_text_pattern(self, issues: List[AccessibilityIssue]) -> Dict[str, Dict[str, Any]]:
        """
        Группирует проблемы по текстовым паттернам
        Возвращает словарь: {текст_паттерн: {страницы: [], проблемы: [], символы: 0, типы: set()}}
        """
        text_groups = defaultdict(lambda: {
            'pages': set(),
            'issues': [],
            'total_words': 0,
            'issue_types': set(),
            'severities': defaultdict(int),
            'descriptions': set(),
            'font_info': set()
        })

        for issue in issues:
            # Нормализуем текст для группировки - убираем дубли
            text_key = self.normalize_text_for_grouping(issue.text)

            # Пропускаем слишком короткие или бессмысленные тексты
            if len(text_key) < 5:
                continue

            # Если текст слишком длинный, обрезаем
            if len(text_key) > 50:
                text_key = self.truncate_text_smart(text_key, 50)

            group = text_groups[text_key]
            group['pages'].add(issue.page)
            group['issues'].append(issue)
            group['total_words'] += self.count_words(text_key)  # Подсчитываем слова
            group['issue_types'].add(issue.issue_type)
            group['severities'][issue.severity] += 1
            group['descriptions'].add(issue.description[:100])  # Первые 100 символов описания

            # Информация о шрифте
            if issue.font_name and issue.font_size:
                font_info = f"{issue.font_name} ({issue.font_size:.1f}pt)"
                group['font_info'].add(font_info)

        # Фильтруем группы, которые встречаются на нескольких страницах или много раз
        filtered_groups = {}
        for text_key, data in text_groups.items():
            if len(data['pages']) >= 2 or len(data['issues']) >= 3:  # Уменьшил порог с 5 до 3
                # Сортируем страницы
                data['pages_sorted'] = sorted(data['pages'])
                data['total_pages'] = len(data['pages'])
                data['total_issues'] = len(data['issues'])
                filtered_groups[text_key] = data

        return filtered_groups

    def generate_text_pattern_report(self, issues_by_type: Dict[str, List[AccessibilityIssue]]) -> str:
        """Генерирует отчет по текстовым паттернам"""

        report = "\n📋 ГРУППИРОВКА ПО ПОВТОРЯЮЩИМСЯ ТЕКСТАМ:\n"
        report += "=" * 80 + "\n"

        all_pattern_reports = []

        for issue_type, issues in issues_by_type.items():
            if not issues:
                continue

            # Группируем проблемы этого типа по текстовым паттернам
            text_groups = self.group_issues_by_text_pattern(issues)

            if not text_groups:
                continue

            type_report = f"\n🔍 {issue_type.upper()} - повторяющиеся тексты:\n"
            type_report += "-" * 60 + "\n"

            # Сортируем группы по количеству страниц и проблем
            sorted_groups = sorted(
                text_groups.items(),
                key=lambda x: (len(x[1]['pages']), len(x[1]['issues'])),
                reverse=True
            )

            for i, (text_pattern, data) in enumerate(sorted_groups[:10], 1):  # Показываем топ-10
                type_report += f"\n{i}. Текст: \"{text_pattern}\"\n"

                # Страницы, где встречается
                pages_list = data['pages_sorted']
                if len(pages_list) <= 10:
                    pages_str = ", ".join(str(p) for p in pages_list)
                else:
                    pages_str = f"{pages_list[0]}-{pages_list[-1]} (всего {len(pages_list)} страниц)"

                type_report += f"   📄 Встречается на страницах: {pages_str}\n"
                type_report += f"   📊 Статистика: {data['total_issues']} мест, {data['total_words']:,} слов\n"

                # Серьезность
                severity_info = []
                for severity, count in data['severities'].items():
                    icon = '🔴' if severity == 'high' else ('🟡' if severity == 'medium' else '🟢')
                    severity_info.append(f"{icon}{count}")

                if severity_info:
                    type_report += f"   ⚠️  Серьезность: {' '.join(severity_info)}\n"

                # Информация о шрифтах
                if data['font_info']:
                    fonts = list(data['font_info'])[:3]  # Показываем до 3 шрифтов
                    if len(fonts) == 1:
                        type_report += f"   🔤 Шрифт: {fonts[0]}\n"
                    else:
                        type_report += f"   🔤 Шрифты: {', '.join(fonts)}\n"

                # Типичное описание проблемы
                if data['descriptions']:
                    # Берем самое частое или первое описание
                    desc = list(data['descriptions'])[0]
                    if len(desc) > 100:
                        desc = desc[:97] + "..."
                    type_report += f"   📝 Проблема: {desc}\n"

            all_pattern_reports.append(type_report)

        if not all_pattern_reports:
            report += "\n⚠️  Повторяющихся текстовых паттернов не обнаружено\n"
        else:
            report += "\n".join(all_pattern_reports)

        return report

    def generate_color_report_improved(self) -> str:
        """Генерирует улучшенный отчет по проблемным цветам с группировкой"""
        if not self.color_issues:
            return ""

        report = "\n🎨 ОТЧЕТ ПО ПРОБЛЕМНЫМ ЦВЕТАМ:\n"
        report += "=" * 80 + "\n\n"

        # Группируем по цветам и тексту
        color_text_groups = defaultdict(lambda: defaultdict(lambda: {
            'pages': defaultdict(int),
            'total_count': 0,
            'issues': [],
            'contrasts': []
        }))

        for issue in self.color_issues:
            # Нормализуем текст
            if 'full_text' in issue:
                normalized_text = self.normalize_text_for_grouping(issue['full_text'])
            elif 'text_sample' in issue:
                normalized_text = self.normalize_text_for_grouping(issue['text_sample'])
            else:
                continue

            if len(normalized_text) < 5:
                continue

            color_name = issue['color_name']
            color_text_groups[color_name][normalized_text]['pages'][issue['page']] += 1
            color_text_groups[color_name][normalized_text]['total_count'] += 1
            color_text_groups[color_name][normalized_text]['issues'].append(issue)
            color_text_groups[color_name][normalized_text]['contrasts'].append(issue['contrast'])

        for color_name, text_groups in sorted(color_text_groups.items()):
            total_issues = sum(len(data['issues']) for data in text_groups.values())
            total_texts = len(text_groups)

            report += f"\n{color_name.upper()} (всего {total_issues} случаев, {total_texts} уникальных текстов):\n"
            report += "-" * 60 + "\n"

            # Сортируем тексты по частоте встречаемости
            sorted_texts = sorted(
                text_groups.items(),
                key=lambda x: (x[1]['total_count'], len(x[1]['pages'])),
                reverse=True
            )[:10]  # Показываем топ-10

            for i, (text, data) in enumerate(sorted_texts, 1):
                # Обрезаем длинный текст
                text_preview = text[:60] + ("..." if len(text) > 60 else "")

                # Собираем информацию о страницах
                pages_list = list(data['pages'].keys())
                if len(pages_list) <= 5:
                    pages_str = ", ".join(str(p) for p in sorted(pages_list))
                    pages_info = f"на стр. {pages_str}"
                else:
                    pages_info = f"на {len(pages_list)} стр. (первая: стр. {sorted(pages_list)[0]})"

                # Средняя контрастность
                avg_contrast = sum(data['contrasts']) / len(data['contrasts'])

                report += f"\n{i}. Текст: \"{text_preview}\"\n"
                report += f"   📊 Встречается: {data['total_count']} раз {pages_info}\n"
                report += f"   🎨 Средняя контрастность: {avg_contrast:.1f}:1"

                # Статистика по контрастности
                below_45 = sum(1 for c in data['contrasts'] if c < 4.5)

                if below_45 > 0:
                    percentage = (below_45 / len(data['contrasts'])) * 100
                    report += f" (ниже 4.5:1 - {below_45} случаев, {percentage:.0f}%)"

                report += "\n"

                # Информация о первом экземпляре
                if data['issues']:
                    first_issue = data['issues'][0]
                    if 'font_size' in first_issue:
                        report += f"   📏 Размер шрифта: {first_issue['font_size']:.1f}pt"
                        if first_issue.get('is_large', False):
                            report += " (крупный текст)"
                        report += "\n"

        # Рекомендации по цветам
        report += "\n💡 РЕКОМЕНДАЦИИ ПО ИСПРАВЛЕНИЮ ЦВЕТОВ:\n"
        report += "-" * 60 + "\n"
        report += "1. Зеленый текст на белом фоне:\n"
        report += "   • Проблема: светло-зеленый, салатовый (контрастность ~2.9-3.5:1)\n"
        report += "   • Решение: используйте темно-зеленый (#006400, #228B22)\n"
        report += "   • Результат: контрастность ~6.5:1 ✓\n\n"

        report += "2. Серый текст на белом фоне:\n"
        report += "   • Проблема: средне-серый (контрастность ~3.9:1)\n"
        report += "   • Решение: используйте темно-серый (#333333) или черный (#000000)\n"
        report += "   • Результат: контрастность 12.6:1 или 21:1 ✓\n\n"

        report += "3. Желтый/оранжевый текст:\n"
        report += "   • Проблема: яркий желтый/оранжевый (контрастность ~3.0:1)\n"
        report += "   • Решение: используйте темные оттенки или замените на черный\n\n"

        report += "4. Лучшие сочетания для доступности:\n"
        report += "   • Черный (#000000) на белом: 21:1 ✓\n"
        report += "   • Темно-серый (#333333) на белом: 12.6:1 ✓\n"
        report += "   • Темно-синий (#000066) на белом: 8.6:1 ✓\n"
        report += "   • Темно-зеленый (#006400) на белом: 6.5:1 ✓\n"

        return report

    def generate_summary_table(self, issues: List[AccessibilityIssue]) -> str:
        """Генерирует сводную таблицу проблем"""
        if not issues:
            return ""

        # Группируем проблемы
        text_groups = self.group_issues_by_text_and_page(issues)

        report = "\n📋 СВОДНАЯ ТАБЛИЦА ПРОБЛЕМ (ГРУППИРОВКА ПО ТЕКСТУ):\n"
        report += "=" * 80 + "\n\n"
        report += "№ | Текст | Проблема | Страницы | Количество | Серьезность\n"
        report += "-" * 80 + "\n"

        # Сортируем по количеству встречаемости
        sorted_groups = sorted(
            text_groups.items(),
            key=lambda x: x[1]['total_count'],
            reverse=True
        )[:50]  # Показываем топ-50

        for i, (text, data) in enumerate(sorted_groups, 1):
            first_issue = data['first_issue']
            if not first_issue:
                continue

            # Обрезаем текст
            text_preview = text[:40] + ("..." if len(text) > 40 else "")

            # Описание проблемы
            description = list(data['descriptions'])[0] if data['descriptions'] else ""
            desc_preview = description[:50] + ("..." if len(description) > 50 else "")

            # Информация о страницах
            pages_list = list(data['pages'].keys())
            if len(pages_list) <= 3:
                pages_str = ", ".join(str(p) for p in sorted(pages_list))
            else:
                pages_str = f"{pages_list[0]}, ..., {pages_list[-1]} ({len(pages_list)} стр.)"

            # Серьезность с иконкой
            severity_icon = '🔴' if first_issue.severity == 'high' else (
                '🟡' if first_issue.severity == 'medium' else '🟢')

            report += f"{i:2d} | {text_preview:42s} | {desc_preview:48s} | {pages_str:15s} | {data['total_count']:4d} раз | {severity_icon} {first_issue.severity}\n"

        return report

    def analyze(self) -> List[AccessibilityIssue]:
        """Основной метод анализа PDF"""
        print(f"🔍 Начинаю улучшенный анализ доступности PDF: {self.pdf_path}")

        try:
            with pdfplumber.open(self.pdf_path) as pdf:
                total_pages = len(pdf.pages)
                print(f"📄 Найдено страниц: {total_pages}")

                for page_num, page in enumerate(pdf.pages, 1):
                    print(f"  Анализ страницы {page_num}/{total_pages}...", end='\r')

                    # Очищаем кэш для новой страницы
                    self.line_cache.clear()
                    self.full_text_cache.clear()

                    page_issues = self.analyze_page(page_num, page)
                    self.issues.extend(page_issues)

                print(f"\n✅ Анализ завершен. Найдено проблем: {len(self.issues)}")

        except Exception as e:
            print(f"\n❌ Ошибка при анализе PDF: {e}")
            import traceback
            traceback.print_exc()

        return self.issues

    def generate_summary_report(self) -> str:
        """Генерирует краткий отчет с основной статистикой"""
        summary = self.group_and_summarize_issues_improved()
        
        report = "📊 КРАТКИЙ ОТЧЕТ ПО ДОСТУПНОСТИ PDF\n"
        report += "=" * 60 + "\n\n"
        report += f"📄 Документ: {os.path.basename(self.pdf_path)}\n"
        report += f"📈 Всего проблем: {summary['overall']['total_places']:,} мест\n"
        report += f"📊 Всего слов проблемного текста: {summary['overall']['total_words']:,}\n"
        report += f"📑 Затронуто страниц: {len(summary['overall']['pages_with_issues'])}\n\n"
        
        # Статистика по серьезности
        report += "📊 СТАТИСТИКА ПО СЕРЬЕЗНОСТИ:\n"
        report += "-" * 40 + "\n"
        for severity in ['high', 'medium', 'low']:
            if severity in summary['by_severity']:
                group = summary['by_severity'][severity]
                icon = '🔴' if severity == 'high' else ('🟡' if severity == 'medium' else '🟢')
                report += f"{icon} {severity.upper()}: {group['places']:,} мест ({group['words']:,} слов)\n"
        
        # Топ-3 типа проблем
        report += "\n📋 ОСНОВНЫЕ ТИПЫ ПРОБЛЕМ:\n"
        report += "-" * 40 + "\n"
        type_items = sorted(
            summary['by_type'].items(),
            key=lambda x: x[1]['total_places'],
            reverse=True
        )[:3]
        
        for issue_type, type_data in type_items:
            report += f"• {issue_type}: {type_data['total_places']:,} мест ({type_data['total_words']:,} слов)\n"
        
        return report

    def generate_json_report(self) -> Dict[str, Any]:
        """Генерирует отчет в формате JSON"""
        summary = self.group_and_summarize_issues_improved()
        
        # Конвертируем issues в словари
        issues_dict = [asdict(issue) for issue in self.issues]
        
        # Конвертируем sets в lists для JSON
        def convert_sets(obj):
            if isinstance(obj, set):
                return sorted(list(obj))
            elif isinstance(obj, dict):
                return {k: convert_sets(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [convert_sets(item) for item in obj]
            return obj
        
        convert_sets(summary)  # Подготовка для будущего использования
        
        report = {
            'document': os.path.basename(self.pdf_path),
            'document_path': self.pdf_path,
            'analysis_date': datetime.now().isoformat(),
            'summary': {
                'total_issues': summary['overall']['total_places'],
                'total_words': summary['overall']['total_words'],
                'pages_affected': sorted(list(summary['overall']['pages_with_issues'])),
                'by_severity': {
                    sev: {
                        'places': data['places'],
                        'words': data['words']
                    }
                    for sev, data in summary['by_severity'].items()
                },
                'by_type': {
                    issue_type: {
                        'total_places': data['total_places'],
                        'total_words': data['total_words'],
                        'pages_affected': sorted(list(data['pages_affected']))
                    }
                    for issue_type, data in summary['by_type'].items()
                }
            },
            'issues': issues_dict[:1000],  # Ограничиваем для JSON (первые 1000)
            'color_issues': self.color_issues[:100]  # Ограничиваем цветовые проблемы
        }
        
        return report

    def generate_statistics_only_report(self) -> str:
        """Генерирует отчет только со статистикой без деталей"""
        summary = self.group_and_summarize_issues_improved()
        
        report = "📊 СТАТИСТИКА ПО ДОСТУПНОСТИ PDF\n"
        report += "=" * 60 + "\n\n"
        report += f"📄 Документ: {os.path.basename(self.pdf_path)}\n"
        report += f"📈 Всего проблем: {summary['overall']['total_places']:,} мест\n"
        report += f"📊 Всего слов проблемного текста: {summary['overall']['total_words']:,}\n"
        report += f"📑 Затронуто страниц: {len(summary['overall']['pages_with_issues'])}\n\n"
        
        # Детальная статистика по типам и серьезности
        report += "📋 РАСПРЕДЕЛЕНИЕ ПО ТИПАМ И СЕРЬЕЗНОСТИ:\n"
        report += "-" * 60 + "\n"
        
        for issue_type, severity_data in sorted(
            summary['by_type_severity'].items(),
            key=lambda x: sum(v['places'] for v in x[1].values()),
            reverse=True
        ):
            total = sum(v['places'] for v in severity_data.values())
            if total == 0:
                continue
            
            report += f"\n{issue_type}:\n"
            for severity in ['high', 'medium', 'low']:
                if severity_data[severity]['places'] > 0:
                    icon = '🔴' if severity == 'high' else ('🟡' if severity == 'medium' else '🟢')
                    places = severity_data[severity]['places']
                    pct = (places / total) * 100
                    report += f"  {icon} {severity.capitalize()}: {places:,} мест ({pct:.1f}%)\n"
        
        return report

    def generate_improved_report(self, output_file: str = None,
                                 create_screenshots: bool = False,
                                 screenshot_mode: str = "smart",
                                 report_format: str = "full") -> str:
        """
        Генерирует улучшенный отчет с четким разделением по типам и серьезности

        Args:
            output_file: путь для сохранения отчета
            create_screenshots: создавать ли скриншоты
            screenshot_mode: режим создания скриншотов:
                - "none": не создавать скриншоты
                - "area": создавать скриншоты проблемных областей
                - "full_page": создавать полностаничные скриншоты
                - "smart": комбинированный режим
            report_format: формат отчета:
                - "full": полный подробный отчет (по умолчанию)
                - "summary": краткий отчет
                - "statistics": только статистика
                - "json": JSON формат
        """
        
        # Обработка разных форматов отчета
        if report_format == "summary":
            report = self.generate_summary_report()
            if output_file:
                with open(output_file, 'w', encoding='utf-8') as f:
                    f.write(report)
                print(f"\n📁 Краткий отчет сохранен в файл: {output_file}")
            print("\n" + "=" * 60)
            print(report)
            return report
        
        elif report_format == "statistics":
            report = self.generate_statistics_only_report()
            if output_file:
                with open(output_file, 'w', encoding='utf-8') as f:
                    f.write(report)
                print(f"\n📁 Статистический отчет сохранен в файл: {output_file}")
            print("\n" + "=" * 60)
            print(report)
            return report
        
        elif report_format == "json":
            report_dict = self.generate_json_report()
            report_json = json.dumps(report_dict, ensure_ascii=False, indent=2)
            if output_file:
                with open(output_file, 'w', encoding='utf-8') as f:
                    f.write(report_json)
                print(f"\n📁 JSON отчет сохранен в файл: {output_file}")
            else:
                print(report_json)
            return report_json
        
        # Продолжаем с полным отчетом (report_format == "full")

        # Группируем с улучшенной структурой
        summary = self.group_and_summarize_issues_improved()

        # Подсчитываем уникальные места
        unique_locations = set()
        for issue in self.issues:
            location_key = f"{issue.page}_{issue.x:.1f}_{issue.y:.1f}_{self.remove_duplicate_chars(issue.text[:50])}"
            unique_locations.add(location_key)

        report = "📊 УЛУЧШЕННЫЙ ОТЧЕТ ПО ДОСТУПНОСТИ PDF\n"
        report += "=" * 80 + "\n\n"
        report += f"📄 Документ: {self.pdf_path}\n"
        report += f"📈 Всего проблем: {summary['overall']['total_places']:,} мест\n"
        report += f"📊 Всего слов проблемного текста: {summary['overall']['total_words']:,}\n"
        report += f"📑 Затронуто страниц: {len(summary['overall']['pages_with_issues'])}\n"

        if not self.issues:
            report += "\n✅ Проблем с доступностью не обнаружено!\n"
            report += "Документ соответствует основным требованиям WCAG 2.1.\n"
        else:
            # ==================== СВОДНАЯ СТАТИСТИКА ====================
            report += "\n📊 СВОДНАЯ СТАТИСТИКА:\n"
            report += "=" * 40 + "\n"

            for severity in ['high', 'medium', 'low']:
                if severity in summary['by_severity']:
                    group = summary['by_severity'][severity]
                    icon = '🔴' if severity == 'high' else ('🟡' if severity == 'medium' else '🟢')

                    report += f"\n{icon} {severity.upper()}: {group['places']:,} мест ({group['words']:,} слов)\n"

                    # Распределение по типам внутри серьезности
                    if group['types']:
                        for issue_type, type_data in sorted(group['types'].items(),
                                                            key=lambda x: x[1]['places'],
                                                            reverse=True):
                            report += f"   • {issue_type}: {type_data['places']:,} мест ({type_data['words']:,} слов)\n"

            # ==================== РАСПРЕДЕЛЕНИЕ ПО ТИПАМ ====================
            report += "\n\n📋 РАСПРЕДЕЛЕНИЕ ПО ТИПАМ ПРОБЛЕМ (с детализацией по серьезности):\n"
            report += "=" * 60 + "\n"

            # Сортируем типы по общему количеству мест
            type_items = sorted(
                summary['by_type_severity'].items(),
                key=lambda x: (
                    sum(v['places'] for v in x[1].values()),  # всего мест
                    sum(v['words'] for v in x[1].values())  # всего слов
                ),
                reverse=True
            )

            for issue_type, severity_data in type_items:
                # Суммарная статистика по типу
                total_places = sum(v['places'] for v in severity_data.values())
                total_words = sum(v['words'] for v in severity_data.values())

                if total_places == 0:
                    continue

                report += f"\n{issue_type.upper()}:\n"
                report += f"  Всего: {total_places:,} мест ({total_words:,} слов)\n"

                # Детализация по серьезности
                for severity in ['high', 'medium', 'low']:
                    if severity_data[severity]['places'] > 0:
                        icon = '🔴' if severity == 'high' else ('🟡' if severity == 'medium' else '🟢')
                        places = severity_data[severity]['places']
                        words = severity_data[severity]['words']
                        percentage = (places / total_places) * 100 if total_places > 0 else 0

                        report += f"  {icon} {severity.capitalize()}: {places:,} мест ({words:,} слов, {percentage:.1f}%)\n"

            # ==================== ДЕТАЛЬНЫЙ АНАЛИЗ КАЖДОГО ТИПА ====================
            report += "\n\n🔍 ДЕТАЛЬНЫЙ АНАЛИЗ ПО ТИПАМ ПРОБЛЕМ:\n"
            report += "=" * 60 + "\n"

            issues_by_type = defaultdict(list)
            for issue in self.issues:
                issues_by_type[issue.issue_type].append(issue)

            for issue_type, type_issues in sorted(issues_by_type.items(),
                                                  key=lambda x: len(x[1]),
                                                  reverse=True):
                if len(type_issues) < 10:  # Пропускаем редкие типы
                    continue

                # Статистика по этому типу
                type_summary = summary['by_type'][issue_type]

                report += f"\n{issue_type.upper()} ({type_summary['total_places']:,} мест):\n"
                report += "-" * 40 + "\n"

                # Для проблем с контрастностью используем специальную группировку
                if issue_type == 'Контрастность':
                    # Группируем по тексту
                    text_groups = self.group_issues_by_text_and_page(type_issues)

                    # Сортируем по частоте встречаемости
                    sorted_groups = sorted(
                        text_groups.items(),
                        key=lambda x: x[1]['total_count'],
                        reverse=True
                    )[:20]  # Показываем топ-20 самых частых

                    for i, (text, group_data) in enumerate(sorted_groups, 1):
                        first_issue = group_data['first_issue']
                        total_count = group_data['total_count']
                        pages_count = len(group_data['pages'])

                        # Берем пример описания
                        description = list(group_data['descriptions'])[0] if group_data['descriptions'] else ""

                        # Формируем информацию о страницах
                        if pages_count <= 5:
                            pages_list = list(group_data['pages'].keys())
                            pages_str = ", ".join(str(p) for p in sorted(pages_list))
                            pages_info = f"на страницах: {pages_str}"
                        else:
                            pages_list = sorted(group_data['pages'].keys())
                            pages_info = f"на {pages_count} страницах (первая: стр. {pages_list[0]})"

                        # Обрезаем текст для отображения
                        text_preview = text[:80] + ("..." if len(text) > 80 else "")

                        report += f"\n{i}. Текст: \"{text_preview}\"\n"
                        report += f"   📝 Проблема: {description[:100]}\n"
                        report += f"   📊 Встречается: {total_count} раз {pages_info}\n"

                        if first_issue:
                            icon = '🔴' if first_issue.severity == 'high' else (
                                '🟡' if first_issue.severity == 'medium' else '🟢')
                            report += f"   {icon} Серьезность: {first_issue.severity}\n"
                            if first_issue.font_name:
                                report += f"   🔤 Шрифт: {first_issue.font_name} ({first_issue.font_size:.1f}pt)\n"
                else:
                    # Для других типов проблем используем старый формат
                    report += f"📄 Затронуто страниц: {len(type_summary['pages_affected'])}\n"

                    # Топ-5 страниц по количеству проблем
                    page_counts = defaultdict(int)
                    for issue in type_issues:
                        page_counts[issue.page] += 1

                    if page_counts:
                        top_pages = sorted(page_counts.items(), key=lambda x: x[1], reverse=True)[:5]
                        report += f"📊 Самые проблемные страницы:\n"
                        for page_num, count in top_pages:
                            report += f"   • Страница {page_num}: {count:,} мест\n"

                    # Примеры проблем
                    report += f"\n🔎 ПРИМЕРЫ ПРОБЛЕМ:\n"

                    # Берем примеры с разной серьезностью
                    examples_by_severity = {'high': [], 'medium': [], 'low': []}
                    for issue in type_issues[:50]:
                        examples_by_severity[issue.severity].append(issue)

                    examples_shown = 0
                    for severity in ['high', 'medium', 'low']:
                        for issue in examples_by_severity[severity][:2]:
                            text_preview = self.remove_duplicate_chars(issue.text)
                            text_preview = text_preview[:80] + ("..." if len(text_preview) > 80 else "")
                            icon = '🔴' if severity == 'high' else ('🟡' if severity == 'medium' else '🟢')

                            report += f"\n   {icon} {severity.capitalize()}: {text_preview}\n"
                            report += f"      📝 {issue.description[:120]}\n"
                            examples_shown += 1

                        if examples_shown >= 6:
                            break

            # ==================== ВЫВОД ПО СТРАНИЦАМ ====================
            report += "\n\n📄 ОБЗОР ПО СТРАНИЦАМ (топ-10 самых проблемных):\n"
            report += "=" * 60 + "\n"

            # Собираем статистику по страницам
            page_stats = defaultdict(lambda: {
                'total_places': 0,
                'total_words': 0,
                'by_type': defaultdict(lambda: {'places': 0, 'words': 0}),
                'by_severity': defaultdict(int)
            })

            for issue in self.issues:
                page = page_stats[issue.page]
                word_count = self.count_words(issue.text)
                page['total_places'] += 1
                page['total_words'] += word_count
                page['by_type'][issue.issue_type]['places'] += 1
                page['by_type'][issue.issue_type]['words'] += word_count
                page['by_severity'][issue.severity] += 1

            # Сортируем страницы по количеству проблем
            sorted_pages = sorted(
                page_stats.items(),
                key=lambda x: x[1]['total_places'],
                reverse=True
            )[:10]  # Только топ-10

            for page_num, stats in sorted_pages:
                report += f"\n📄 СТРАНИЦА {page_num}:\n"
                report += f"   Всего: {stats['total_places']:,} мест ({stats['total_words']:,} слов)\n"

                # Распределение по серьезности
                sev_str = []
                for sev in ['high', 'medium', 'low']:
                    if sev in stats['by_severity'] and stats['by_severity'][sev] > 0:
                        icon = '🔴' if sev == 'high' else ('🟡' if sev == 'medium' else '🟢')
                        sev_str.append(f"{icon}{stats['by_severity'][sev]}")

                if sev_str:
                    report += f"   ⚠️  Серьезность: {' '.join(sev_str)}\n"

                # Основные типы проблем
                type_items = sorted(
                    stats['by_type'].items(),
                    key=lambda x: x[1]['places'],
                    reverse=True
                )[:3]  # Только топ-3 типа

                for issue_type, type_data in type_items:
                    if type_data['places'] > 0:
                        report += f"   • {issue_type}: {type_data['places']:,} мест ({type_data['words']:,} слов)\n"

        # Отчет по проблемным цветам (если есть проблемы с контрастностью)
        if 'Контрастность' in summary['by_type_severity']:
            color_report = self.generate_color_report_improved()
            if color_report:
                report += color_report

        # Добавляем сводную таблицу
        report += self.generate_summary_table(self.issues)

        # Рекомендации
        report += "\n💡 ОБЩИЕ РЕКОМЕНДАЦИИ ПО ИСПРАВЛЕНИЮ:\n"
        report += "=" * 60 + "\n"

        # Анализируем, какие типы проблем присутствуют
        issue_types_present = set(summary['by_type_severity'].keys())

        if 'Контрастность' in issue_types_present:
            report += "1. УВЕЛИЧЬТЕ КОНТРАСТНОСТЬ ТЕКСТА:\n"
            report += "   • Обычный текст: минимальная контрастность 4.5:1\n"
            report += "   • Крупный текст (≥18pt или ≥14pt жирный): минимальная контрастность 3.0:1\n"
            report += "   • Используйте: черный (#000000), темно-серый (#333333), темно-синий (#000066)\n\n"

        if 'Размер шрифта' in issue_types_present:
            report += "2. УВЕЛИЧЬТЕ РАЗМЕР ШРИФТА:\n"
            report += "   • Основной текст: минимальный размер 12pt (рекомендуется 14-16pt)\n"
            report += "   • Заголовки: минимальный размер 14pt (рекомендуется 16-18pt)\n"
            report += "   • Для слабовидящих: основной текст 16-18pt, заголовки 20-24pt\n\n"

        if 'Читаемость шрифта' in issue_types_present:
            report += "3. ВЫБЕРИТЕ ЧИТАЕМЫЕ ШРИФТЫ:\n"
            report += "   • Рекомендуется: Arial, Verdana, Tahoma, Georgia\n"
            report += "   • Избегайте: декоративных, моноширинных, рукописных шрифтов\n\n"

        report += "📋 СТАНДАРТЫ WCAG 2.1 (Уровень AA):\n"
        report += "   • Контрастность текста: 4.5:1 (3.0:1 для крупного текста)\n"
        report += "   • Минимальный размер текста: эффективный визуальный размер 2.5мм\n"
        report += "   • Использование цвета: не полагаться только на цвет для передачи информации\n"

        # Вывод в консоль
        print("\n" + "=" * 80)
        print(report)

        # Сохранение в файл
        if output_file:
            with open(output_file, 'w', encoding='utf-8') as f:
                f.write(report)
            print(f"\n📁 Отчет сохранен в файл: {output_file}")

        return report


# ИСПОЛЬЗОВАНИЕ
if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description='Анализатор визуальной доступности PDF файлов',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Примеры использования:
  python main.py document.pdf
  python main.py document.pdf --format summary
  python main.py document.pdf --format json --output report.json
  python main.py document.pdf --format statistics --screenshots
  
  python main.py  # Запуск без аргументов покажет это сообщение
        """
    )
    
    # Путь по умолчанию из оригинального кода
    default_pdf_path = r"C:\Users\vikharev-d\Downloads\Telegram Desktop\2_5291784456137378049.pdf"
    
    parser.add_argument(
        'pdf_path',
        type=str,
        nargs='?',  # Делаем аргумент опциональным
        default=default_pdf_path,
        help=f'Путь к PDF файлу для анализа (по умолчанию: {os.path.basename(default_pdf_path)})'
    )
    
    parser.add_argument(
        '--format', '-f',
        type=str,
        choices=['full', 'summary', 'statistics', 'json'],
        default='full',
        help='Формат отчета: full (полный), summary (краткий), statistics (только статистика), json (JSON формат)'
    )
    
    parser.add_argument(
        '--output', '-o',
        type=str,
        default=None,
        help='Путь для сохранения отчета (по умолчанию: автоматическое имя файла)'
    )
    
    parser.add_argument(
        '--screenshots', '-s',
        action='store_true',
        help='Создавать скриншоты проблемных областей'
    )
    
    parser.add_argument(
        '--screenshot-mode',
        type=str,
        choices=['none', 'area', 'full_page', 'smart'],
        default='smart',
        help='Режим создания скриншотов: none, area, full_page, smart'
    )
    
    args = parser.parse_args()
    
    # Используем путь из аргументов или по умолчанию
    pdf_path = args.pdf_path
    
    # Проверяем существование файла
    if not os.path.exists(pdf_path):
        print(f"❌ Ошибка: Файл не найден: {pdf_path}")
        print(f"\n💡 Проверьте правильность пути к файлу.")
        print(f"💡 Убедитесь, что файл существует и доступен для чтения.")
        print(f"\n💡 Использование:")
        print(f"  python main.py [путь_к_pdf_файлу] [опции]")
        print(f"  python main.py --help  # для просмотра всех опций")
        exit(1)
    
    # Проверяем, что это PDF файл
    if not pdf_path.lower().endswith('.pdf'):
        print(f"⚠️  Предупреждение: Файл не имеет расширения .pdf: {pdf_path}")
        response = input("Продолжить анализ? (y/n): ").strip().lower()
        if response != 'y':
            print("Анализ отменен.")
            exit(0)
    
    # Проверяем доступность файла для чтения
    if not os.access(pdf_path, os.R_OK):
        print(f"❌ Ошибка: Нет доступа для чтения файла: {pdf_path}")
        print(f"💡 Проверьте права доступа к файлу.")
        exit(1)
    
    # Генерируем имя файла отчета, если не указано
    if args.output is None:
        base_name = os.path.splitext(os.path.basename(pdf_path))[0]
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        
        if args.format == 'json':
            args.output = f"reports/{base_name}_report_{timestamp}.json"
        elif args.format == 'summary':
            args.output = f"reports/{base_name}_summary_{timestamp}.txt"
        elif args.format == 'statistics':
            args.output = f"reports/{base_name}_statistics_{timestamp}.txt"
        else:
            args.output = f"reports/{base_name}_full_report_{timestamp}.txt"
        
        # Создаем папку reports, если её нет
        os.makedirs('reports', exist_ok=True)
    
    # Создаем улучшенный анализатор
    analyzer = EnhancedPDFAccessibilityAnalyzer(pdf_path)

    # Проводим анализ
    print("🚀 Запуск анализа доступности...")
    print(f"📄 Файл: {pdf_path}")
    print(f"📊 Формат отчета: {args.format}")
    print("-" * 60)
    
    issues = analyzer.analyze()

    # Генерируем отчет в выбранном формате
    report = analyzer.generate_improved_report(
        output_file=args.output,
        create_screenshots=args.screenshots,
        screenshot_mode=args.screenshot_mode if args.screenshots else "none",
        report_format=args.format
    )

    # Дополнительная статистика
    if analyzer.issues:
        summary = analyzer.group_and_summarize_issues_improved()

        print("\n📊 ИТОГОВАЯ СТАТИСТИКА:")
        print("-" * 40)

        print(f"Общий объем проблемного текста: {summary['overall']['total_words']:,} слов")

        # Подсчет уникальных текстов (нормализованных)
        unique_texts = set()
        for issue in analyzer.issues:
            normalized = analyzer.remove_duplicate_chars(issue.text)
            unique_texts.add(normalized[:100])  # Используем первые 100 символов

        print(f"Уникальных текстовых фрагментов: {len(unique_texts):,}")

        print("\nСамые проблемные страницы (по объему текста):")
        # Группируем по страницам
        page_words = defaultdict(int)
        page_issues = defaultdict(int)

        for issue in analyzer.issues:
            page_words[issue.page] += analyzer.count_words(issue.text)
            page_issues[issue.page] += 1

        sorted_pages = sorted(page_words.items(), key=lambda x: x[1], reverse=True)[:5]

        for page_num, words in sorted_pages:
            issues_count = page_issues[page_num]
            print(f"\n  📄 Страница {page_num}:")
            print(f"    • Всего слов: {words:,}")
            print(f"    • Всего проблем: {issues_count:,}")
            if issues_count > 0:
                print(f"    • Средний текст на проблему: {words / issues_count:.1f} слов")

    if analyzer.color_issues:
        print("\n🎨 СВОДКА ПО ЦВЕТАМ (нормализованные тексты):")
        color_summary = defaultdict(lambda: {'count': 0, 'unique_texts': set(), 'words': 0})
        for issue in analyzer.color_issues:
            color = issue['color_name']
            color_summary[color]['count'] += 1
            text = issue.get('normalized_text', '') or issue.get('full_text', '') or issue.get('text_sample', '')
            if text:
                color_summary[color]['unique_texts'].add(text[:100])
                color_summary[color]['words'] += analyzer.count_words(text)

        for color, stats in sorted(color_summary.items(), key=lambda x: x[1]['words'], reverse=True):
            print(
                f"  {color}: {stats['count']:,} случаев, {len(stats['unique_texts']):,} уникальных текстов, {stats['words']:,} слов")
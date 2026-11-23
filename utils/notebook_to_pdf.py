"""
Converts the chapter notebooks into PDFs typeset like the printed book.

The notebook is turned into HTML (markdown-it, Pygments, latex2mathml),
printed by headless Chrome using ``pdf_assets/book.css`` and finished
with PyMuPDF (table of contents page numbers, running footers,
bookmarks, page labels).
"""

import base64
import hashlib
import html
import json
import os
import re
import shutil
import struct
import subprocess
import tempfile
import unicodedata
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from pathlib import Path
from typing import Annotated, Any, Optional

import pymupdf
import typer
from fontTools.pens.cu2quPen import Cu2QuPen
from fontTools.pens.ttGlyphPen import TTGlyphPen
from fontTools.ttLib import TTFont, newTable
from latex2mathml.converter import convert as latex_to_mathml
from markdown_it import MarkdownIt
from markdown_it.renderer import RendererHTML
from markdown_it.rules_core import StateCore
from markdown_it.token import Token
from mdit_py_plugins.dollarmath import dollarmath_plugin
from pygments import highlight
from pygments.formatters import HtmlFormatter
from pygments.lexers import TextLexer, get_lexer_by_name
from pygments.style import Style
from pygments.token import (
    Comment,
    Error,
    Generic,
    Keyword,
    Literal,
    Name,
    Number,
    Operator,
    Punctuation,
    String,
    Text,
)
from pygments.util import ClassNotFound

ROOT_DIR = Path(__file__).resolve().parents[1]
ASSETS_DIR = Path(__file__).resolve().parent / 'pdf_assets'
CSS_PATH = ASSETS_DIR / 'book.css'
ICONS_DIR = ASSETS_DIR / 'icons'

# Chrome snaps layout to whole CSS pixels (0.75pt), so pages are laid
# out SCALE times larger and scaled back down to PAGE_SIZE afterwards
SCALE = 3
PAGE_SIZE = (504, 661.5)
LENGTH_RE = re.compile(r'(?<![\w.#])(-?(?:\d+(?:\.\d+)?|\.\d+))(pt|px)\b')
TAG_RE = re.compile(r'<[a-zA-Z][^<>]*>')
SIZE_ATTR_RE = re.compile(r'\b(width|height)="(\d+(?:\.\d+)?)"')
STYLE_ATTR_RE = re.compile(r'\bstyle="[^"]*"')
COLUMN_WIDTH = 360
MAX_FIGURE_WIDTH = 345.6
FIGURE_DPI = 300
OUTPUT_FIGURE_DPI = 150

# Shrinks the DataFrames that are wider than the text column. The script
# runs before the print layout, so the column width (in CSS px) is given
FIT_TABLES_JS = f'''
const column = {COLUMN_WIDTH * SCALE * 4 / 3:g};
for (const table of document.querySelectorAll('.output-html table')) {{
  const width = table.getBoundingClientRect().width;
  if (width > column) {{
    table.style.zoom = Math.floor(1000 * column / width) / 1000;
  }}
}}
'''

ADMONITIONS = ('note', 'tip', 'warning')
CAPTION_RE = re.compile(
    r'(?P<kind>Equations?|Eqautions?|Examples?|Tables?|Figures?)'
    r'\s+(?P<number>\d+[-–]\d+(?:\s*(?:,|and|to|–|-)\s*\d+[-–]\d+)*)'
    r'[.:]?'
)
CHAPTER_RE = re.compile(r'Chapter\s+(?P<number>\d+)\s*[-–—:]\s*(?P<title>.+)')
BADGE_RE = re.compile(r'^\[!\[[^\]]*\]\([^)]*\)\]\([^)]*\)[ \t]*\n?', re.M)
CENTER_IMG_RE = re.compile(r'<center>\s*(<img\b.*?>)\s*</center>', re.S)
STYLE_TAG_RE = re.compile(r'<style\b[^>]*>.*?</style>[ \t]*\n?', re.S)
# ``ul {list-style-type: none;}``, or ``*:not(li) > ul {...}`` for only
# the top level lists
PLAIN_LISTS_RE = re.compile(
    r'(?P<top>\*:not\(li\)\s*>\s*)?ul\s*\{\s*list-style(?:-type)?:\s*none'
)
SIDEBAR_RE = re.compile(
    r'\A\s*<div\s+style="(?P<style>[^"]*border[^"]*)">[ \t]*\n'
    r'(?P<body>.*?)\n?\s*</div>\s*\Z',
    re.S,
)
ANSI_RE = re.compile(r'\x1b\[[0-9;?]*[A-Za-z]')

MATHML_NS = 'http://www.w3.org/1998/Math/MathML'
ET.register_namespace('', MATHML_NS)
# Operators drawn with the math font: they need to stretch or grow
LARGE_OPERATORS = set('∑∏∐∫∬∭∮⋃⋂⋁⋀⨁⨂√')
MATH_STYLES = {'BOLD ITALIC': 'bfit', 'BOLD': 'bf', 'ITALIC': 'it'}
VARIANT_STYLES = {
    'bold': 'bf',
    'bold-italic': 'bfit',
    'italic': 'it',
    'normal': 'up',
}


class BookStyle(Style):
    """Syntax highlighting colors of the code listings in the book."""

    background_color = 'transparent'
    styles = {
        Keyword: 'bold #006699',
        Keyword.Pseudo: 'nobold',
        Keyword.Type: 'bold #007788',
        Name: '#000088',
        Name.Attribute: '#330099',
        Name.Builtin: '#336666',
        Name.Class: 'bold #00AA88',
        Name.Constant: '#336600',
        Name.Decorator: '#9999FF',
        Name.Entity: 'bold #999999',
        Name.Exception: 'bold #CC0000',
        Name.Function: '#CC00FF',
        Name.Label: '#9999FF',
        Name.Namespace: 'bold #00CCFF',
        Name.Property: '#9966FF',
        Name.Tag: 'bold #330099',
        Name.Variable: '#003333',
        Operator: '#555555',
        Operator.Word: 'bold #000000',
        Punctuation: '#000000',
        String: '#CC3300',
        String.Doc: 'italic',
        String.Escape: 'bold',
        String.Interpol: '#AA0000',
        String.Regex: '#33AAAA',
        String.Symbol: '#AA6600',
        Number: '#FF6600',
        Literal: '#FF9900',
        Comment: 'italic #0099FF',
        Comment.Single: '#35586C',
        Comment.Multiline: '#35586C',
        Comment.Special: 'bold #35586C',
        Comment.Preproc: 'noitalic #009999',
        Generic.Heading: 'bold #003300',
        Generic.Subheading: 'bold #003300',
        Generic.Prompt: 'bold #000099',
        Generic.Output: '#000000',
        Generic.Traceback: '#99CC66',
        Generic.Deleted: 'bg:#FFCCCC',
        Generic.Inserted: 'bg:#CCFFCC',
        Generic.Emph: 'italic',
        Generic.Strong: 'bold',
        Text.Whitespace: '#BBBBBB',
        Error: '',
    }


@dataclass
class Heading:
    """A heading that goes into the table of contents and bookmarks."""

    level: int
    id: str
    title: str


@dataclass
class _Sidebar:
    parts: list[str]
    titled: bool = False


def _escape(text: str) -> str:
    return html.escape(text, quote=False)


def _roman(number: int) -> str:
    numerals = [
        (1000, 'm'),
        (900, 'cm'),
        (500, 'd'),
        (400, 'cd'),
        (100, 'c'),
        (90, 'xc'),
        (50, 'l'),
        (40, 'xl'),
        (10, 'x'),
        (9, 'ix'),
        (5, 'v'),
        (4, 'iv'),
        (1, 'i'),
    ]
    result = ''
    for value, numeral in numerals:
        while number >= value:
            result += numeral
            number -= value
    return result


def _png_size(data: bytes) -> tuple[int, int]:
    return struct.unpack('>II', data[16:24])


def _join(text: str | list[str]) -> str:
    return text if isinstance(text, str) else ''.join(text)


def _plain_lists(source: str) -> Optional[str]:
    """
    Which bullet lists the style tags of a markdown cell hide the
    bullets of: ``'all'``, only the ``'top'`` level ones, or none.
    """
    plain = None
    for tag in STYLE_TAG_RE.findall(source):
        for match in PLAIN_LISTS_RE.finditer(tag):
            plain = 'top' if match['top'] and plain != 'all' else 'all'
    return plain


def _separate_math_blocks(source: str) -> str:
    """
    Puts blank lines around ``$$`` blocks: unlike LaTeX in Jupyter,
    dollarmath doesn't let them interrupt a paragraph.
    """
    lines: list[str] = []
    in_fence, in_math = False, False
    for line in source.split('\n'):
        stripped = line.strip()
        if stripped.startswith(('```', '~~~')) and not in_math:
            in_fence = not in_fence
        elif not in_fence and stripped.startswith('$$') and not in_math:
            if lines and lines[-1].strip():
                lines.append('')
            single_line = len(stripped) > 2 and stripped.endswith('$$')
            in_math = not single_line
            lines.extend([line, ''] if single_line else [line])
            continue
        elif in_math and stripped.endswith('$$'):
            in_math = False
            lines.extend([line, ''])
            continue
        lines.append(line)
    return '\n'.join(lines)


# ---------------------------------------------------------------- fonts

# (CSS family, weight, style, PostScript name) of the book's fonts
FONT_FACES = [
    ('Book Serif', 400, 'normal', 'MinionPro-Regular'),
    ('Book Serif', 400, 'italic', 'MinionPro-It'),
    ('Book Serif', 600, 'normal', 'MinionPro-Semibold'),
    ('Book Serif', 700, 'normal', 'MinionPro-Bold'),
    ('Book Serif', 700, 'italic', 'MinionPro-BoldIt'),
    ('Book Sans', 400, 'normal', 'MyriadPro-Cond'),
    ('Book Sans', 400, 'italic', 'MyriadPro-CondIt'),
    ('Book Sans', 600, 'normal', 'MyriadPro-SemiboldCond'),
    ('Book Sans', 600, 'italic', 'MyriadPro-SemiboldCondIt'),
    ('Book Sans', 700, 'normal', 'MyriadPro-BoldCond'),
    ('Book Mono', 400, 'normal', 'UbuntuMono-Regular'),
    ('Book Mono', 400, 'italic', 'UbuntuMono-Italic'),
    ('Book Mono', 700, 'normal', 'UbuntuMono-Bold'),
    ('Book Mono', 700, 'italic', 'UbuntuMono-BoldItalic'),
    ('Book Math', 400, 'normal', 'STIXTwoMath-Regular'),
]
FONT_DIRS = [
    Path.home() / 'Library/Fonts',
    Path('/Library/Fonts'),
    Path('/System/Library/Fonts/Supplemental'),
    Path('/System/Library/Fonts'),
    Path.home() / '.local/share/fonts',
    Path.home() / '.fonts',
    Path('/usr/local/share/fonts'),
    Path('/usr/share/fonts'),
    Path(os.environ.get('WINDIR', 'C:/Windows')) / 'Fonts',
    Path(os.environ.get('LOCALAPPDATA', '.')) / 'Microsoft/Windows/Fonts',
]
FONT_CACHE_DIR = (
    Path(os.environ.get('XDG_CACHE_HOME', Path.home() / '.cache'))
    / 'handson-mlp-notes'
    / 'fonts'
)


def _find_fonts(postscript_names: set[str]) -> dict[str, Path]:
    found: dict[str, Path] = {}
    for font_dir in FONT_DIRS:
        if not font_dir.is_dir():
            continue
        for path in sorted(font_dir.rglob('*')):
            if path.suffix.lower() not in ('.otf', '.ttf'):
                continue
            try:
                name = TTFont(path, lazy=True)['name'].getDebugName(6)
            except Exception:  # Unreadable fonts are just skipped
                continue
            if name in postscript_names and name not in found:
                found[name] = path
                if len(found) == len(postscript_names):
                    return found
    return found


def _to_truetype(source: Path, target: Path) -> None:
    """
    Converts a CFF-flavored OpenType font to TrueType outlines.
    Chrome can only embed TrueType outlines in PDFs and otherwise
    draws the text as Type 3 fonts, which viewers render poorly.
    """
    font = TTFont(source)
    glyph_set = font.getGlyphSet()
    glyphs = {}
    for name in font.getGlyphOrder():
        pen = TTGlyphPen(glyph_set)
        glyph_set[name].draw(Cu2QuPen(pen, 1.0, reverse_direction=True))
        glyphs[name] = pen.glyph()
    font['loca'] = newTable('loca')
    font['glyf'] = glyf = newTable('glyf')
    glyf.glyphOrder = font.getGlyphOrder()
    glyf.glyphs = glyphs
    for table in ('CFF ', 'VORG'):
        if table in font:
            del font[table]
    glyf.compile(font)
    hmtx = font['hmtx']
    for name, glyph in glyphs.items():
        if hasattr(glyph, 'xMin'):
            hmtx[name] = (hmtx[name][0], glyph.xMin)
    font['maxp'] = maxp = newTable('maxp')
    maxp.tableVersion = 0x00010000
    for attribute in (
        'maxZones',
        'maxTwilightPoints',
        'maxStorage',
        'maxFunctionDefs',
        'maxInstructionDefs',
        'maxStackElements',
        'maxSizeOfInstructions',
        'maxComponentElements',
    ):
        setattr(maxp, attribute, 1 if attribute == 'maxZones' else 0)
    font['post'].formatType = 2.0
    font['post'].extraNames = []
    font['post'].mapping = {}
    font['post'].glyphOrder = font.getGlyphOrder()
    font.sfntVersion = '\x00\x01\x00\x00'
    target.parent.mkdir(parents=True, exist_ok=True)
    font.save(target)


def font_face_css() -> str:
    """
    Builds the ``@font-face`` rules of the book's fonts.

    Returns
    -------
    str
        The CSS rules
    """
    paths = _find_fonts({face[3] for face in FONT_FACES})
    rules = []
    for family, weight, style, name in FONT_FACES:
        sources = [f'local("{name}")']
        path = paths.get(name)
        if path is None:
            typer.secho(f'Font not found: {name}', fg='yellow', err=True)
        else:
            if TTFont(path, lazy=True).sfntVersion == 'OTTO':
                converted = FONT_CACHE_DIR / f'{name}.ttf'
                if (
                    not converted.is_file()
                    or converted.stat().st_mtime < path.stat().st_mtime
                ):
                    typer.echo(f'Converting {path.name} to TrueType...')
                    _to_truetype(path, converted)
                path = converted
            sources.insert(0, f'url("{path.as_uri()}")')
        rules.append(
            f'@font-face {{ font-family: "{family}"; font-weight: {weight};'
            f' font-style: {style}; src: {", ".join(sources)}; }}'
        )
    return '\n'.join(rules)


# ---------------------------------------------------------------- math


def _matching_brace(text: str, start: int) -> int:
    depth = 0
    for i in range(start, len(text)):
        if text[i] == '\\':
            continue
        if text[i] == '{' and (i == 0 or text[i - 1] != '\\'):
            depth += 1
        elif text[i] == '}' and text[i - 1] != '\\':
            depth -= 1
            if depth == 0:
                return i
    return len(text) - 1


def _split_text_math(latex: str) -> str:
    r"""
    Rewrites ``\text{a $x$ b}`` (math nested in text, which latex2mathml
    keeps verbatim) as ``\text{a }x\text{ b}``.
    """
    result, position = [], 0
    while (start := latex.find('\\text{', position)) >= 0:
        end = _matching_brace(latex, start + 5)
        inner = latex[start + 6 : end].replace('$\\_$', '_')
        result.append(latex[position:start])
        if '$' in inner:
            for i, part in enumerate(inner.split('$')):
                if i % 2:
                    result.append('{' + part + '}')
                elif part:
                    result.append('\\text{' + part + '}')
        else:
            result.append('\\text{' + inner + '}')
        position = end + 1
    result.append(latex[position:])
    return ''.join(result)


def _plain_letter(description: str, fallback: str) -> str:
    kind, _, letter = description.partition(' ')
    candidates = [description, f'GREEK {description}']
    if kind in ('SMALL', 'CAPITAL'):
        candidates[:0] = [
            f'LATIN {kind} LETTER {letter}',
            f'GREEK {kind} LETTER {letter}',
        ]
    if description.endswith('SYMBOL'):
        candidates.append(f'GREEK LUNATE {description}')
    for candidate in candidates:
        try:
            return unicodedata.lookup(candidate)
        except KeyError:
            pass
    return fallback


def _style_identifier(element: ET.Element) -> None:
    """
    Maps identifiers to the book's text font: Chrome would otherwise use
    Unicode math alphanumerics, which only the math font has.
    """
    style = VARIANT_STYLES.get(element.attrib.pop('mathvariant', ''))
    chars = []
    for char in element.text or '':
        match = re.fullmatch(
            r'MATHEMATICAL (BOLD ITALIC|BOLD|ITALIC) (.+)',
            unicodedata.name(char, ''),
        )
        if match:
            style = MATH_STYLES[match[1]]
            char = _plain_letter(match[2], char)
        chars.append(char)
    text = element.text = ''.join(chars)
    if style is None:
        name = unicodedata.name(text, '') if len(text) == 1 else ''
        is_letter = name.startswith(('LATIN', 'GREEK SMALL', 'GREEK THETA'))
        style = 'it' if is_letter else 'up'
    element.set('mathvariant', 'normal')
    element.set('class', f't {style}')


def _style_math(root: ET.Element) -> None:
    parents = {child: parent for parent in root.iter() for child in parent}
    for element in root.iter():
        tag = element.tag.rpartition('}')[2]
        if tag == 'mi':
            _style_identifier(element)
        elif tag in ('mn', 'mtext'):
            element.set('class', 't')
        elif tag == 'mo':
            parent = parents.get(element)
            is_accent = (
                parent is not None
                and parent.tag.rpartition('}')[2]
                in ('mover', 'munder', 'munderover')
                and list(parent).index(element) > 0
            )
            if (
                element.get('stretchy') != 'true'
                and not is_accent
                and (element.text or '') not in LARGE_OPERATORS
            ):
                element.set('class', 't')


def latex_to_html(latex: str, display: bool) -> str:
    """
    Converts LaTeX math to MathML styled like the book's equations.

    Parameters
    ----------
    latex:
        The LaTeX source without the dollar delimiters
    display:
        Whether the math is a display (block) equation

    Returns
    -------
    str
        The MathML markup
    """
    source = _split_text_math(latex.strip())
    try:
        mathml = latex_to_mathml(
            source, display='block' if display else 'inline'
        )
        root = ET.fromstring(mathml)
    except Exception:  # Keep going: one bad formula shouldn't stop a PDF
        typer.secho(f'Cannot convert math: {latex}', fg='yellow', err=True)
        return f'<code class="bad-math">{_escape(latex)}</code>'
    _style_math(root)
    return ET.tostring(root, encoding='unicode')


# -------------------------------------------------------------- figures


def _scale_lengths(text: str) -> str:
    """Multiplies the ``pt`` and ``px`` lengths in CSS by ``SCALE``."""
    return LENGTH_RE.sub(lambda m: f'{float(m[1]) * SCALE:g}{m[2]}', text)


def _scale_tags(html_text: str) -> str:
    """Scales the lengths in style, width and height attributes."""

    def scale_tag(tag: re.Match) -> str:
        text = STYLE_ATTR_RE.sub(lambda m: _scale_lengths(m[0]), tag[0])
        return SIZE_ATTR_RE.sub(
            lambda m: f'{m[1]}="{float(m[2]) * SCALE:g}"', text
        )

    return TAG_RE.sub(scale_tag, html_text)


def _ebook_figure_widths(ebook_dir: Optional[Path]) -> dict[str, float]:
    """
    Maps image hashes to the figure widths used in the book's EPUB
    (``<figure class="width-70">`` is 70% of the text column).
    """
    widths: dict[str, float] = {}
    if ebook_dir is None or not ebook_dir.is_dir():
        return widths
    pattern = re.compile(r'<figure class="([^"]*)".*?<img src="([^"]+)"', re.S)
    for chapter in ebook_dir.glob('*.html'):
        for classes, src in pattern.findall(chapter.read_text()):
            match = re.search(r'width-(\d+)', classes)
            image = ebook_dir / src
            if match and image.is_file():
                digest = hashlib.md5(image.read_bytes()).hexdigest()
                widths[digest] = int(match[1]) / 100 * COLUMN_WIDTH
    return widths


# ------------------------------------------------------------ converter


class NotebookConverter:
    """
    Renders a notebook to the HTML of a book chapter.

    Parameters
    ----------
    notebook_filepath:
        The notebook filepath
    figure_widths:
        Figure widths (pt) indexed by the MD5 hash of the image file
    font_css:
        The ``@font-face`` rules returned by ``font_face_css``
    """

    def __init__(
        self,
        notebook_filepath: Path,
        figure_widths: dict[str, float],
        font_css: str,
    ) -> None:
        self.path = notebook_filepath.resolve()
        self.font_css = font_css
        self.notebook = json.loads(self.path.read_text())
        self.figure_widths = figure_widths
        self.headings: list[Heading] = []
        self.chapter_number: Optional[str] = None
        self.chapter_title = self.path.stem
        self._ids: set[str] = set()
        language = (
            self.notebook.get('metadata', {})
            .get('language_info', {})
            .get('name', 'python')
        )
        self.language = language
        self.formatter = HtmlFormatter(style=BookStyle, nowrap=True)
        self.md = self._markdown()

    # ----------------------------------------------------- public API

    @property
    def running_title(self) -> str:
        """The running title of the left-hand (verso) pages."""
        if self.chapter_number is None:
            return self.chapter_title
        return f'Chapter {self.chapter_number}: {self.chapter_title}'

    @property
    def toc_headings(self) -> list[Heading]:
        """
        Headings listed in the table of contents (down to sect2),
        without the bare exercise numbers (``### 1.``).
        """
        return [
            h
            for h in self.headings
            if h.level <= 3 and not re.fullmatch(r'\d+\.?', h.title)
        ]

    def render_body(self) -> str:
        """
        Renders all the cells.

        Returns
        -------
        str
            The chapter HTML
        """
        body: list[str] = []
        sidebar: Optional[_Sidebar] = None
        for cell in self.notebook['cells']:
            source = _join(cell.get('source', ''))
            if cell['cell_type'] == 'markdown':
                # The cell's style tags would apply to the whole PDF,
                # only the hidden list bullets are kept
                plain_lists = _plain_lists(source)
                source = STYLE_TAG_RE.sub('', source)
                match = SIDEBAR_RE.match(source)
                if match:
                    style = match['style'].replace(' ', '')
                    if sidebar is None:
                        sidebar = _Sidebar(parts=[])
                    sidebar.parts.append(
                        self._markdown_cell(
                            match['body'], sidebar, plain_lists
                        )
                    )
                    if 'border-bottom:none' not in style:
                        body.append(self._close_sidebar(sidebar))
                        sidebar = None
                    continue
                rendered = self._markdown_cell(source, sidebar, plain_lists)
            elif cell['cell_type'] == 'code':
                rendered = self._code_cell(cell)
            else:
                continue
            (sidebar.parts if sidebar else body).append(rendered)
        if sidebar is not None:
            body.append(self._close_sidebar(sidebar))
        return '\n'.join(body)

    def document(self, body: str, page_numbers: dict[str, str]) -> str:
        """
        Builds the full HTML document: table of contents and chapter.

        Parameters
        ----------
        body:
            The chapter HTML returned by ``render_body``
        page_numbers:
            Page labels of the headings, indexed by heading id

        Returns
        -------
        str
            The HTML document
        """
        entries = []
        for heading in self.toc_headings:
            page = page_numbers.get(heading.id, '')
            title = _escape(heading.title)
            href = f'#{heading.id}'
            if heading.level == 1:
                numbered = self.chapter_number is not None
                number = (
                    f'<span class="num">{self.chapter_number}.</span>'
                    if numbered
                    else ''
                )
                entries.append(
                    f'<a class="entry chapter-entry'
                    f'{" numbered" if numbered else ""}" href="{href}">'
                    f'{number}<span class="title">{title}</span>'
                    f'<span class="leader"></span>'
                    f'<span class="page">{page}</span></a>'
                )
            else:
                entries.append(
                    f'<a class="entry sect{heading.level - 1}-entry" '
                    f'href="{href}"><span class="title">{title}</span>'
                    f'<span class="page">{page}</span></a>'
                )
        toc = '\n'.join(entries)
        return self._html_page(
            '<section class="front">'
            '<div class="opener toc-opener"><h1>Table of Contents</h1></div>'
            f'<nav class="toc">\n{toc}\n</nav></section>\n'
            f'<section class="chapter">\n{body}\n</section>'
        )

    def footer_document(self, footers: list[tuple[str, str]]) -> str:
        """
        Builds a document whose pages only contain the running footers.

        Parameters
        ----------
        footers:
            ``(side, html)`` per page, where side is "recto" or "verso"

        Returns
        -------
        str
            The HTML document
        """
        pages = ''.join(
            f'<div class="footer-page"><div class="footer {side}">'
            f'{content}</div></div>'
            for side, content in footers
        )
        return self._html_page(
            pages, '<style>@page { margin: 0; } body { margin: 0; }</style>'
        )

    # ------------------------------------------------------ rendering

    def _html_page(self, body: str, head: str = '') -> str:
        css = self.formatter.get_token_style_defs('.code')
        book_css = _scale_lengths(CSS_PATH.read_text())
        return (
            '<!DOCTYPE html>\n<html lang="en"><head><meta charset="utf-8">'
            f'<base href="{self.path.parent.as_uri()}/">'
            f'<style>\n{self.font_css}\n</style>'
            f'<style>\n{book_css}\n</style>'
            f'<style>\n{"".join(css)}\n</style>{head}</head>'
            f'<body>\n{_scale_tags(body)}\n'
            f'<script>{FIT_TABLES_JS}</script></body></html>\n'
        )

    def _markdown(self) -> MarkdownIt:
        md = MarkdownIt('commonmark', {'html': True})
        md.enable(['table', 'strikethrough'])
        md.use(dollarmath_plugin, allow_digits=False, double_inline=True)
        md.core.ruler.push('book_blocks', self._mark_blocks)
        rules = {
            'heading_open': self._render_heading_open,
            'heading_close': self._render_heading_close,
            'paragraph_open': self._render_paragraph_open,
            'paragraph_close': self._render_paragraph_close,
            'bullet_list_open': self._render_bullet_list_open,
            'code_block': self._render_code_block,
            'fence': self._render_fence,
            'math_inline': self._render_math_inline,
            'math_inline_double': self._render_math_block,
            'math_block': self._render_math_block,
            'math_block_label': self._render_math_block,
        }
        for name, method in rules.items():
            md.add_render_rule(name, self._as_render_rule(method))
        return md

    @staticmethod
    def _as_render_rule(method: Any) -> Any:
        # markdown-it binds render rules to the renderer, which then
        # becomes the first argument of the (unbound) function
        def rule(
            renderer: RendererHTML,
            tokens: list[Token],
            idx: int,
            options: Any,
            env: dict[str, Any],
        ) -> str:
            return method(renderer, tokens, idx, options, env)

        return rule

    def _markdown_cell(
        self,
        source: str,
        sidebar: Optional[_Sidebar],
        plain_lists: Optional[str] = None,
    ) -> str:
        source = BADGE_RE.sub('', source)
        source = CENTER_IMG_RE.sub(self._figure, source)
        source = _separate_math_blocks(source)
        env = {'sidebar': sidebar, 'plain_lists': plain_lists}
        return self.md.render(source, env)

    def _close_sidebar(self, sidebar: _Sidebar) -> str:
        return '<div class="sidebar">\n' + '\n'.join(sidebar.parts) + '</div>'

    def _figure(self, match: re.Match) -> str:
        tag = match[1]
        src = re.search(r'\bsrc\s*=\s*"([^"]+)"', tag)
        if src is None:
            return match[0]
        path = (self.path.parent / src[1]).resolve()
        width = MAX_FIGURE_WIDTH
        if path.is_file():
            data = path.read_bytes()
            digest = hashlib.md5(data).hexdigest()
            if digest in self.figure_widths:
                width = self.figure_widths[digest]
            elif data.startswith(b'\x89PNG'):
                width = _png_size(data)[0] * 72 / FIGURE_DPI
        width = min(width, MAX_FIGURE_WIDTH)
        return (
            f'\n\n<div class="figure"><img src="{src[1]}" '
            f'style="width: {width:.1f}pt"></div>\n\n'
        )

    def _code_cell(self, cell: dict[str, Any]) -> str:
        parts = []
        source = _join(cell.get('source', '')).rstrip()
        if source:
            parts.append(self._highlight(source, self.language))
        for output in cell.get('outputs', []):
            parts.append(self._output(output))
        return '\n'.join(part for part in parts if part)

    def _highlight(self, code: str, language: str) -> str:
        try:
            lexer = get_lexer_by_name(language or 'text')
        except ClassNotFound:
            lexer = TextLexer()
        code = highlight(code, lexer, self.formatter).rstrip('\n')
        return f'<pre class="code">{code}</pre>'

    def _output(self, output: dict[str, Any]) -> str:
        kind = output['output_type']
        if kind == 'stream':
            if output.get('name') == 'stderr':
                return ''
            return self._plain_output(_join(output['text']))
        if kind == 'error':
            return self._plain_output('\n'.join(output['traceback']))
        data = output.get('data', {})
        if 'application/vnd.jupyter.widget-view+json' in data:
            return ''
        if 'image/png' in data:
            png = _join(data['image/png']).strip()
            width = _png_size(base64.b64decode(png))[0]
            metadata = output.get('metadata', {}).get('image/png', {})
            width = metadata.get('width', width) * 72 / OUTPUT_FIGURE_DPI
            return (
                '<div class="figure output-figure">'
                f'<img src="data:image/png;base64,{png}" '
                f'style="width: {min(width, MAX_FIGURE_WIDTH):.1f}pt"></div>'
            )
        if 'image/svg+xml' in data:
            svg = _join(data['image/svg+xml'])
            return f'<div class="figure output-figure">{svg}</div>'
        # Only DataFrames are kept as HTML, estimator diagrams and
        # widgets fall back to their plain text representation
        if 'text/html' in data and 'class="dataframe"' in _join(
            data['text/html']
        ):
            content = STYLE_TAG_RE.sub('', _join(data['text/html']))
            return f'<div class="output-html">{content}</div>'
        if 'text/markdown' in data:
            return self.md.render(_join(data['text/markdown']), {})
        if 'text/plain' in data:
            return self._plain_output(_join(data['text/plain']))
        return ''

    @staticmethod
    def _plain_output(text: str) -> str:
        text = ANSI_RE.sub('', text).rstrip()
        return f'<pre class="output">{_escape(text)}</pre>' if text else ''

    # ------------------------------------------------------ token pass

    def _unique_id(self, text: str) -> str:
        slug = re.sub(r'[^a-z0-9]+', '-', text.lower()).strip('-') or 'section'
        candidate, n = slug, 1
        while candidate in self._ids:
            n += 1
            candidate = f'{slug}-{n}'
        self._ids.add(candidate)
        return candidate

    def _mark_blocks(self, state: StateCore) -> None:
        tokens = state.tokens
        for i, token in enumerate(tokens):
            if token.type == 'heading_open':
                self._mark_heading(token, tokens[i + 1], state.env)
            elif token.type == 'paragraph_open':
                mark = self._strip_label(tokens[i + 1])
                if mark:
                    token.meta['book'] = tokens[i + 2].meta['book'] = mark

    def _mark_heading(
        self, token: Token, inline: Token, env: dict[str, Any]
    ) -> None:
        level = int(token.tag[1])
        children = inline.children or []
        if level == 1:
            text = children[0].content if children else ''
            match = CHAPTER_RE.fullmatch(text.strip())
            if match and children:
                self.chapter_number = match['number']
                children[0].content = match['title']
            self.chapter_title = ''.join(c.content for c in children).strip()
            token.meta['book'] = ('chapter', self._unique_id('chapter'))
            self.headings.append(
                Heading(1, token.meta['book'][1], self.chapter_title)
            )
            return
        title = ''.join(
            c.content
            for c in children
            if c.type in ('text', 'code_inline', 'math_inline')
        ).strip()
        sidebar: Optional[_Sidebar] = env.get('sidebar')
        if sidebar is not None:
            if not sidebar.titled:
                sidebar.titled = True
                token.meta['book'] = ('sidebar-title', None)
                return
            token.meta['book'] = ('heading', None)
            return
        heading_id = self._unique_id(title)
        token.meta['book'] = ('heading', heading_id)
        self.headings.append(Heading(level, heading_id, title))

    @staticmethod
    def _strip_label(inline: Token) -> Optional[tuple[str, str]]:
        """
        Removes a leading bold label (``**Note**:``,
        ``**Equation 1-1**``) and returns what the paragraph is.
        """
        children = [
            child
            for child in inline.children or []
            if child.type != 'text' or child.content
        ]
        if (
            len(children) < 3
            or children[0].type != 'strong_open'
            or children[1].type != 'text'
            or children[2].type != 'strong_close'
        ):
            return None
        label = children[1].content.strip()
        rest = children[3:]
        while rest and rest[0].type == 'softbreak':
            rest.pop(0)
        if label.rstrip(':').lower() in ADMONITIONS:
            if rest and rest[0].type == 'text':
                rest[0].content = rest[0].content.lstrip(' :')
            inline.children = rest
            return ('admonition', label.rstrip(':').lower())
        match = CAPTION_RE.fullmatch(label)
        if match is None:
            return None
        kind = match['kind'].replace('Eqaution', 'Equation')
        if rest and rest[0].type == 'text':
            rest[0].content = rest[0].content.lstrip(' :.')
        caption = Token('text', '', 0, content=f'{kind} {match["number"]}. ')
        inline.children = [caption, *rest]
        return ('caption', kind.lower().rstrip('s'))

    # --------------------------------------------------- render rules

    def _render_heading_open(
        self,
        renderer: RendererHTML,
        tokens: list[Token],
        idx: int,
        options: Any,
        env: dict[str, Any],
    ) -> str:
        token = tokens[idx]
        kind, heading_id = token.meta.get('book', ('heading', None))
        if kind == 'chapter':
            label = (
                f'<div class="label">Chapter {self.chapter_number}</div>'
                if self.chapter_number
                else ''
            )
            extra = '' if self.chapter_number else ' unnumbered'
            return (
                f'<div class="opener chapter-opener{extra}">{label}'
                f'<h1 id="{heading_id}">'
            )
        if kind == 'sidebar-title':
            return f'<{token.tag} class="sidebar-title">'
        if heading_id:
            return f'<{token.tag} id="{heading_id}">'
        return f'<{token.tag}>'

    def _render_heading_close(
        self,
        renderer: RendererHTML,
        tokens: list[Token],
        idx: int,
        options: Any,
        env: dict[str, Any],
    ) -> str:
        tag = tokens[idx].tag
        return f'</{tag}></div>\n' if tag == 'h1' else f'</{tag}>\n'

    def _render_paragraph_open(
        self,
        renderer: RendererHTML,
        tokens: list[Token],
        idx: int,
        options: Any,
        env: dict[str, Any],
    ) -> str:
        token = tokens[idx]
        mark = token.meta.get('book')
        if mark is None:
            return renderer.renderToken(tokens, idx, options, env)
        kind, name = mark
        if kind == 'admonition':
            icon = (ICONS_DIR / f'{name}.png').as_uri()
            return (
                f'<div class="admonition {name}"><div class="icon">'
                f'<img src="{icon}" alt="{name}"></div>'
                '<div class="body"><p>'
            )
        return f'<p class="caption {name}">'

    def _render_paragraph_close(
        self,
        renderer: RendererHTML,
        tokens: list[Token],
        idx: int,
        options: Any,
        env: dict[str, Any],
    ) -> str:
        mark = tokens[idx].meta.get('book')
        if mark is None:
            return renderer.renderToken(tokens, idx, options, env)
        return '</p></div></div>\n' if mark[0] == 'admonition' else '</p>\n'

    def _render_bullet_list_open(
        self,
        renderer: RendererHTML,
        tokens: list[Token],
        idx: int,
        options: Any,
        env: dict[str, Any],
    ) -> str:
        plain = env.get('plain_lists')
        if plain == 'top':
            depth = sum(
                {'list_item_open': 1, 'list_item_close': -1}.get(t.type, 0)
                for t in tokens[:idx]
            )
            plain = None if depth else plain
        if plain:
            tokens[idx].attrJoin('class', 'plain')
        return renderer.renderToken(tokens, idx, options, env)

    def _render_code_block(
        self,
        renderer: RendererHTML,
        tokens: list[Token],
        idx: int,
        options: Any,
        env: dict[str, Any],
    ) -> str:
        """Indented blocks are either epigraphs or shell commands."""
        lines = tokens[idx].content.rstrip().split('\n')
        if len(lines) > 1 and lines[-1].lstrip().startswith(('—', '--')):
            quote = self.md.renderInline(
                ' '.join(line.strip() for line in lines[:-1])
            )
            attribution = _escape(lines[-1].strip())
            return (
                f'<blockquote class="epigraph"><p>{quote}</p>'
                f'<p class="attribution">{attribution}</p></blockquote>\n'
            )
        code = _escape('\n'.join(lines))
        return f'<pre class="code">{code}</pre>\n'

    def _render_fence(
        self,
        renderer: RendererHTML,
        tokens: list[Token],
        idx: int,
        options: Any,
        env: dict[str, Any],
    ) -> str:
        token = tokens[idx]
        language = token.info.strip().split(' ')[0] or 'text'
        return self._highlight(token.content.rstrip('\n'), language) + '\n'

    def _render_math_inline(
        self,
        renderer: RendererHTML,
        tokens: list[Token],
        idx: int,
        options: Any,
        env: dict[str, Any],
    ) -> str:
        return latex_to_html(tokens[idx].content, display=False)

    def _render_math_block(
        self,
        renderer: RendererHTML,
        tokens: list[Token],
        idx: int,
        options: Any,
        env: dict[str, Any],
    ) -> str:
        math = latex_to_html(tokens[idx].content, display=True)
        if tokens[idx].type == 'math_inline_double':
            return f'<span class="math-display">{math}</span>'
        return f'<div class="math-display">{math}</div>\n'


# ---------------------------------------------------------- PDF output


def find_chrome(chrome: Optional[Path] = None) -> Path:
    """
    Finds a Chrome or Chromium executable.

    Parameters
    ----------
    chrome:
        An explicit executable path, which takes precedence

    Returns
    -------
    Path
        The executable path
    """
    candidates = [
        chrome,
        os.environ.get('CHROME_PATH'),
        '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
        '/Applications/Chromium.app/Contents/MacOS/Chromium',
        shutil.which('google-chrome'),
        shutil.which('google-chrome-stable'),
        shutil.which('chromium'),
        shutil.which('chromium-browser'),
    ]
    for candidate in candidates:
        if candidate and Path(candidate).is_file():
            return Path(candidate)
    raise typer.BadParameter('Chrome not found, use --chrome or CHROME_PATH')


def print_to_pdf(chrome: Path, html_text: str, pdf_filepath: Path) -> None:
    """
    Prints an HTML document to PDF with headless Chrome.

    Parameters
    ----------
    chrome:
        The Chrome executable
    html_text:
        The HTML document
    pdf_filepath:
        Where to write the PDF
    """
    with tempfile.TemporaryDirectory() as tmp:
        html_filepath = Path(tmp) / 'document.html'
        html_filepath.write_text(html_text)
        subprocess.run(
            [
                str(chrome),
                '--headless',
                '--disable-gpu',
                '--no-first-run',
                '--no-pdf-header-footer',
                '--allow-file-access-from-files',
                f'--user-data-dir={Path(tmp) / "profile"}',
                f'--print-to-pdf={pdf_filepath}',
                html_filepath.as_uri(),
            ],
            check=True,
            capture_output=True,
            timeout=300,
        )


def _link_targets(doc: pymupdf.Document) -> dict[str, tuple[int, float]]:
    """Page index and top (PDF units) of every TOC link target."""
    targets = {}
    for page in doc:
        for link in page.get_links():
            name = link.get('nameddest')
            if name and link.get('page', -1) >= 0:
                targets.setdefault(name, (link['page'], link['to'].y))
    return targets


def _downscale(doc: pymupdf.Document) -> None:
    """
    Scales the pages, laid out ``SCALE`` times larger, down to the book
    size. Internal links are rewritten as explicit destinations since
    Chrome's named destinations point to the unscaled positions.
    """
    width, height = PAGE_SIZE
    page_links = []
    for page in doc:
        scale = width / page.rect.width
        offset = height - page.rect.height * scale
        links = page.get_links()
        for link in links:
            page.delete_link(link)
        page_links.append((links, scale, page.rect.height))
        contents = page.get_contents()
        transform = f'q {scale:.6f} 0 0 {scale:.6f} 0 {offset:.4f} cm\n'
        doc.update_stream(
            contents[0], transform.encode() + doc.xref_stream(contents[0])
        )
        doc.update_stream(contents[-1], doc.xref_stream(contents[-1]) + b'\nQ')
        page.set_mediabox(pymupdf.Rect(0, 0, width, height))
    # Links are inserted once all pages (including targets) are resized
    for page, (links, scale, raw_height) in zip(doc, page_links):
        for link in links:
            new_link = {'kind': link['kind'], 'from': link['from'] * scale}
            if 'uri' in link:
                new_link['uri'] = link['uri']
            elif link.get('page', -1) >= 0:
                # Chrome's destinations use PDF (bottom-up) coordinates
                y = link.get('to', pymupdf.Point(0, raw_height)).y
                new_link.update(
                    kind=pymupdf.LINK_GOTO,
                    page=link['page'],
                    to=pymupdf.Point(0, (raw_height - y) * scale),
                    zoom=0,
                )
            else:
                continue
            page.insert_link(new_link)
    doc.xref_set_key(doc.pdf_catalog(), 'Dests', 'null')


class _Pagination:
    def __init__(self, toc_pages: int, front_matter: bool) -> None:
        self.toc_pages = toc_pages
        self.front_matter = front_matter

    def number(self, index: int) -> int:
        if index < self.toc_pages or self.front_matter:
            return index + 1
        return index - self.toc_pages + 1

    def label(self, index: int) -> str:
        number = self.number(index)
        if index < self.toc_pages or self.front_matter:
            return _roman(number)
        return str(number)


def _footers(
    converter: NotebookConverter,
    pagination: _Pagination,
    heading_pages: dict[str, int],
    page_count: int,
) -> list[tuple[str, str]]:
    sect1_pages = [
        (heading_pages[h.id], h.title)
        for h in converter.headings
        if h.level == 2 and h.id in heading_pages
    ]
    footers = []
    section = converter.chapter_title
    for index in range(page_count):
        label = pagination.label(index)
        recto = pagination.number(index) % 2 == 1
        side = 'recto' if recto else 'verso'
        on_page = [title for page, title in sect1_pages if page == index]
        # Right-hand pages show the first section starting on the page,
        # or else the section continuing from the previous pages
        section_title = on_page[0] if on_page else section
        section = on_page[-1] if on_page else section
        if index in (0, pagination.toc_pages):
            footers.append((side, label))
            continue
        if index < pagination.toc_pages:
            title = 'Table of Contents'
        elif recto:
            title = section_title
        else:
            title = converter.running_title
        title, sep = _escape(title), '<span class="sep">|</span>'
        content = f'{title}{sep}{label}' if recto else f'{label}{sep}{title}'
        footers.append((side, content))
    return footers


def convert_notebook(
    notebook_filepath: Path,
    pdf_filepath: Path,
    chrome: Path,
    figure_widths: dict[str, float],
    font_css: str,
) -> bool:
    """
    Converts a notebook into a book-like PDF.

    Parameters
    ----------
    notebook_filepath:
        The notebook filepath
    pdf_filepath:
        The output PDF filepath
    chrome:
        The Chrome executable
    figure_widths:
        Figure widths (pt) indexed by the MD5 hash of the image file
    font_css:
        The ``@font-face`` rules returned by ``font_face_css``

    Returns
    -------
    bool
        Whether the PDF was created or changed
    """
    converter = NotebookConverter(notebook_filepath, figure_widths, font_css)
    body = converter.render_body()
    with tempfile.TemporaryDirectory() as tmp:
        main_pdf, footer_pdf = Path(tmp) / 'main.pdf', Path(tmp) / 'foot.pdf'
        # Two passes: the first finds on which page each heading lands
        numbers = {h.id: '000' for h in converter.toc_headings}
        for _ in range(4):
            print_to_pdf(chrome, converter.document(body, numbers), main_pdf)
            doc = pymupdf.open(main_pdf)
            targets = _link_targets(doc)
            heading_pages = {key: page for key, (page, _) in targets.items()}
            chapter_id = converter.headings[0].id
            pagination = _Pagination(
                heading_pages[chapter_id], converter.chapter_number is None
            )
            new_numbers = {
                h.id: pagination.label(heading_pages[h.id])
                for h in converter.toc_headings
                if h.id in heading_pages
            }
            if new_numbers == numbers:
                break
            numbers = new_numbers
            doc.close()

        footers = _footers(converter, pagination, heading_pages, len(doc))
        print_to_pdf(chrome, converter.footer_document(footers), footer_pdf)
        overlay = pymupdf.open(footer_pdf)
        if len(overlay) != len(doc):
            raise RuntimeError('Footer pages do not match document pages')
        for index, page in enumerate(doc):
            page.show_pdf_page(page.rect, overlay, index)
        raw_height = doc[0].rect.height
        _downscale(doc)

        bookmarks: list[list[Any]] = [[1, 'Table of Contents', 1]]
        for heading in converter.toc_headings:
            title = heading.title
            if heading.level == 1 and converter.chapter_number:
                title = f'{converter.chapter_number}. {title}'
            page, top = targets[heading.id]
            destination = {
                'kind': pymupdf.LINK_GOTO,
                'page': page,
                'to': pymupdf.Point(0, (raw_height - top) / SCALE),
                'zoom': 0,
            }
            bookmarks.append([heading.level, title, page + 1, destination])
        doc.set_toc(bookmarks)
        labels = [{'startpage': 0, 'prefix': '', 'style': 'r'}]
        if not pagination.front_matter:
            labels.append(
                {
                    'startpage': pagination.toc_pages,
                    'prefix': '',
                    'style': 'D',
                    'firstpagenum': 1,
                }
            )
        doc.set_page_labels(labels)
        doc.set_metadata(
            {
                'title': converter.running_title,
                'subject': 'Notes on Hands-On Machine Learning with '
                'Scikit-Learn and PyTorch',
                'creator': 'handson-mlp-notes',
                'producer': f'PyMuPDF {pymupdf.__version__}',
                'creationDate': '',
                'modDate': '',
            }
        )
        # No dates or random file ID, so unchanged notebooks give
        # byte-identical PDFs
        doc.xref_set_key(-1, 'ID', 'null')
        data = doc.tobytes(garbage=3, deflate=True, no_new_id=True)
        doc.close()
    if pdf_filepath.is_file() and pdf_filepath.read_bytes() == data:
        return False
    pdf_filepath.parent.mkdir(parents=True, exist_ok=True)
    pdf_filepath.write_bytes(data)
    return True


def main(
    notebook_filepaths: Annotated[
        list[Path], typer.Argument(exists=True, dir_okay=False)
    ],
    output_dir: Annotated[Path, typer.Option(file_okay=False)] = Path('pdfs'),
    chrome: Annotated[
        Optional[Path], typer.Option(exists=True, dir_okay=False)
    ] = None,
    ebook_dir: Annotated[
        Optional[Path], typer.Option(exists=True, file_okay=False)
    ] = None,
    fail_on_change: bool = False,
) -> None:
    """
    Converts Jupyter Notebooks into PDFs that look like the book.

    Parameters
    ----------
    notebook_filepaths:
        The notebook filepaths
    output_dir:
        Where to write the PDFs (one per notebook)
    chrome:
        The Chrome/Chromium executable (found automatically by default)
    ebook_dir:
        An extracted EPUB of the book, used for the figure widths
        (defaults to ``ebook_mlp`` when it exists)
    fail_on_change:
        Exit with status 1 when a PDF is created or changed (used by the
        pre-commit hook, which does not notice new untracked files)
    """
    chrome_path = find_chrome(chrome)
    figure_widths = _ebook_figure_widths(ebook_dir or ROOT_DIR / 'ebook_mlp')
    font_css = font_face_css()
    changed = False
    for notebook_filepath in notebook_filepaths:
        pdf_filepath = output_dir / f'{notebook_filepath.stem}.pdf'
        if convert_notebook(
            notebook_filepath,
            pdf_filepath,
            chrome_path,
            figure_widths,
            font_css,
        ):
            changed = True
            typer.echo(f'{notebook_filepath} -> {pdf_filepath}')
        else:
            typer.echo(f'{pdf_filepath} is up to date')
    if fail_on_change and changed:
        raise typer.Exit(1)


if __name__ == '__main__':
    typer.run(main)

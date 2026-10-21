#!/usr/bin/env python3
"""Fold the Verso literate site for BorshSpec.Spec into one self-contained HTML file.

Verso writes a small static site: one page plus separate stylesheets, scripts, a
hover-documentation JSON file and a site-wide search index.  This script keeps the
page exactly as Verso rendered it (same highlighted code, same prose, same hover
tooltips) and does only mechanical packaging:

  * inlines the stylesheets and scripts the page needs,
  * inlines the hover data that the page would otherwise `fetch` (which browsers
    refuse for file:// URLs),
  * drops the site search, the math renderer and the one-entry module sidebar,
  * rewrites the in-page links so they work without a <base> element,
  * adds a few CSS rules (below) that tidy how docstrings sit inside code boxes.

Usage: single-file.py SITE_DIR OUT_FILE
Standard library only.
"""
import json
import re
import sys
from pathlib import Path

PAGE = "BorshSpec/Spec/index.html"
TITLE = "The Borsh format, in one file"

# Rules added after Verso's own stylesheet.
EXTRA_CSS = """
/* single-file page: one module, so no sidebar, breadcrumbs or menu button */
.sidebar, .hamburger, .menu-toggle, .title-bar, .skip-link { display: none !important; }
.layout::after { display: none !important; }

/* Verso draws docstrings inside code boxes between literal `/--` and `-/`
   markers that wrap onto separate lines.  Show them as quiet prose notes. */
.code-box .md-text::before, .code-box .md-text::after,
.code-box .verso-text::before, .code-box .verso-text::after { content: none !important; }
.code-box .md-text, .code-box .verso-text {
  width: auto;
  max-width: 46em;
  border-left: 3px solid var(--verso-docstring-border-color, #ddd);
  padding-left: 0.9rem;
  margin: 0.15rem 0 0.35rem calc(var(--indent, 0) * 1ch);
  color: var(--verso-text-color, inherit);
  font-size: 0.93rem;
  line-height: 1.5;
}
.code-box .md-text > *, .code-box .verso-text > * { margin-bottom: 0.25rem; }
.code-box .md-text > :last-child, .code-box .verso-text > :last-child { margin-bottom: 0; }
.code-box .md-text code, .code-box .verso-text code {
  background: rgba(127, 127, 127, 0.15);
  padding: 0 0.25em;
  border-radius: 3px;
  font-size: 0.9em;
}
"""


def read(site: Path, rel: str) -> str:
    return (site / rel).read_text(encoding="utf-8")


def js(text: str) -> str:
    # A literal "</script" inside inline JavaScript would end the element early.
    return text.replace("</script", "<\\/script")


def main() -> int:
    site, out = Path(sys.argv[1]), Path(sys.argv[2])
    html = read(site, PAGE)

    # Links: pages are addressed relative to <base href="../../">; keep only in-page anchors.
    html = re.sub(r'\s*<base href="[^"]*">', "", html)
    html = html.replace('href="BorshSpec/Spec/#', 'href="#')

    # Stylesheets: inline the three Verso needs, drop the rest (search, math).
    def link(m):
        href = m.group(1)
        if href in ("verso-vars.css", "literate.css", "tippy-border.css"):
            return "<style>\n" + read(site, href) + "\n</style>"
        return ""

    html = re.sub(r'<link rel="stylesheet" href="([^"]+)">', link, html)

    # Scripts: inline the hover/markdown machinery, drop search and math.
    def script(m):
        src = m.group(1)
        if src in ("popper.js", "tippy.js", "marked.js", "copy-button.js"):
            return "<script>\n" + js(read(site, src)) + "\n</script>"
        return ""

    html = re.sub(r'<script(?: type="module")?(?: defer="defer")? src="([^"]+)"(?: defer="defer")?></script>',
                  script, html)

    # Hover data: embed it and read it from the page instead of fetching it.
    docs = json.dumps(json.loads(read(site, "-verso-docs.json")), separators=(",", ":"))
    docs = docs.replace("</", "<\\/")
    html, n = re.subn(r'await \(fetch\("-verso-docs\.json"\)\.then\(\(resp\) => resp\.json\(\)\)\)',
                      'JSON.parse(document.getElementById("verso-docs").textContent)', html)
    assert n == 1, "hover-data fetch not found; Verso's page template changed"
    html = html.replace("</head>",
                        f'<script type="application/json" id="verso-docs">{docs}</script>\n'
                        f"<style>{EXTRA_CSS}</style>\n</head>", 1)

    html = re.sub(r"<title>.*?</title>", f"<title>{TITLE}</title>", html, count=1)

    # The module-tree sidebar and breadcrumbs link to other pages that do not exist here.
    # They are hidden by CSS; remove them from the markup as well so no dead links remain.
    html = re.sub(r"<aside class=\"sidebar\">.*?</aside>", "", html, count=1, flags=re.S)
    html = re.sub(r"<header class=\"title-bar\">.*?</header>", "", html, count=1, flags=re.S)

    # Self-containment check: nothing may point at a file next to the page.
    markup = re.sub(r"<(script|style)\b.*?</\1>", "", html, flags=re.S)
    leftovers = re.findall(r'(?:src|href)="(?!#|data:|https?://)([^"]+)"', markup)
    if leftovers:
        sys.exit(f"not self-contained, relative references remain: {sorted(set(leftovers))}")
    css = "".join(re.findall(r"<style>(.*?)</style>", html, flags=re.S))
    css_refs = [u for u in re.findall(r"url\(\s*['\"]?([^'\")]+)", css) if not u.startswith("data:")]
    if css_refs or re.search(r"@import", css):
        sys.exit(f"stylesheet references outside files: {css_refs}")
    external = sorted(set(re.findall(r'(?:src|href)="(https?://[^"]+)"', markup)))
    if external:
        sys.exit(f"external references remain: {external}")

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(html, encoding="utf-8")
    print(f"wrote {out} ({len(html) // 1024} KiB), no external references")
    return 0


if __name__ == "__main__":
    sys.exit(main())

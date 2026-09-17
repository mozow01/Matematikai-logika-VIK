project = "Matematikai logika"
copyright = "2026, Molnár Zoltán"
author = "Molnár Zoltán"

extensions = [
    "sphinx.ext.autosectionlabel",
    "sphinx.ext.mathjax",
    "sphinx_copybutton",
    "myst_parser",
]

myst_enable_extensions = [
    "colon_fence",
    "deflist",
    "fieldlist",
]

language = "hu"
templates_path = ["_templates"]
exclude_patterns = ["_build", "Thumbs.db", ".DS_Store"]

html_theme = "sphinx_rtd_theme"
html_title = "Matematikai logika"
html_baseurl = "https://mozow01.github.io/Matematikai-logika-VIK/"
html_static_path = ["_static"]
html_css_files = ["css/custom.css", "css/lesson2-practice.css"]
html_js_files = [
    "js/interactive-frames.js",
    "js/practice.js",
    "js/lesson2-practice.js",
]

html_context = {
    "display_github": True,
    "github_user": "mozow01",
    "github_repo": "Matematikai-logika-VIK",
    "github_version": "main",
    "conf_py_path": "/docs/",
}

html_theme_options = {
    "collapse_navigation": False,
    "navigation_depth": 4,
    "titles_only": False,
}

autosectionlabel_prefix_document = True
numfig = True

copybutton_selector = "div.highlight-text pre, div.highlight-coq pre"
copybutton_exclude = ".linenos, .gp, .go"

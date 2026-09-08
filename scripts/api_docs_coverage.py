#!/usr/bin/env python3
"""Check that the generated API docs are complete and current.

The documented inventory is the transitive import closure of `InfinitaryLogic.Everything`: the
default surface (`InfinitaryLogic.All`), the `Conditional/` bundle, and the legacy off-path
modules that CI builds. The work-in-progress library (`InfinitaryLogic.WIP`) is not documented.
The docs workflow generates exactly that inventory (`lake build InfinitaryLogic.Everything:docs`).

Three checks, run after generation in `docbuild/` and repeatable against the deployed site's
`docs/` directory:

1. **Coverage**: every module of the inventory has a page, and no page exists for a module with
   no source file (a removed module must not keep a page).
2. **Content sentinels**: named declarations must appear as anchors in named pages. Exact page
   coverage cannot tell an old version of a page from a current one; a sentinel from each recent
   change can. Update `SENTINELS` when a sentinel declaration moves or is renamed.
3. **Retired pages**: pages for retired modules must be absent.

`--self-test` builds a synthetic docs tree in a temporary directory and checks that the script
passes on a complete tree and fails when one page, one declaration anchor, or the retired-page
condition is broken. Not a `scripts/check_*` guard: it needs the generated docs, so the docs
workflow runs it explicitly.

Usage:
  python3 scripts/api_docs_coverage.py [DOC_DIR]      (default docbuild/.lake/build/doc)
  python3 scripts/api_docs_coverage.py --self-test
"""
from __future__ import annotations

import pathlib
import re
import sys
import tempfile

ROOT = 'InfinitaryLogic.Everything'
LIB = 'InfinitaryLogic'
IMPORT_RE = re.compile(r'^\s*import\s+(InfinitaryLogic(?:\.[A-Za-z0-9_]+)*)\s*$', re.M)

# (page relative to DOC_DIR, fully qualified declaration name expected as an anchor id).
SENTINELS = [
    ('InfinitaryLogic/Descriptive/FragmentTail.html',
     'FirstOrder.Language.sentenceTheory_image_countable_of_determining_cover'),
    ('InfinitaryLogic/Descriptive/WellOrderThin.html',
     'FirstOrder.Language.kbLanguage.wellOrderClass_isThinOn'),
    ('InfinitaryLogic/Conditional/SentenceSpectrum.html',
     'FirstOrder.Language.thin_iff_countable_sentence_spectra'),
]

# Pages that must not exist (modules retired from the library).
RETIRED_PAGES = [
    'InfinitaryLogic/Admissible/Barwise/ConsistencyBridge.html',
]


def module_path(mod: str) -> pathlib.Path:
    return pathlib.Path(*mod.split('.')).with_suffix('.lean')


def closure(root: str, src_root: pathlib.Path) -> set[str]:
    seen, todo = set(), [root]
    while todo:
        mod = todo.pop()
        if mod in seen:
            continue
        seen.add(mod)
        src = src_root / module_path(mod)
        if not src.exists():
            sys.exit(f'module {mod} imported but {src} does not exist')
        todo.extend(IMPORT_RE.findall(src.read_text()))
    return seen


def page_of(mod: str) -> str:
    return mod.replace('.', '/') + '.html'


def anchor_present(page: pathlib.Path, decl: str) -> bool:
    text = page.read_text(errors='replace')
    return f'id="{decl}"' in text or f"id='{decl}'" in text


def check(doc: pathlib.Path, src_root: pathlib.Path) -> list[str]:
    """Return a list of problems; empty means the docs pass."""
    problems: list[str] = []
    inventory = closure(ROOT, src_root)
    expected = {page_of(m) for m in inventory}
    pages = {p.relative_to(doc).as_posix() for p in (doc / LIB).rglob('*.html')}
    if (doc / f'{LIB}.html').exists():
        pages.add(f'{LIB}.html')
    sources = {page_of(p.relative_to(src_root).with_suffix('').as_posix().replace('/', '.'))
               for p in (src_root / LIB).rglob('*.lean')} | {f'{LIB}.html'}
    missing = sorted(expected - pages)
    orphan = sorted(pages - sources)
    if missing:
        problems.append(f'missing pages ({len(missing)}): {missing}')
    if orphan:
        problems.append(f'pages without a source module: {orphan}')
    for rel, decl in SENTINELS:
        page = doc / rel
        if not page.exists():
            problems.append(f'sentinel page missing: {rel}')
        elif not anchor_present(page, decl):
            problems.append(f'sentinel declaration {decl} not found in {rel} (stale page?)')
    for rel in RETIRED_PAGES:
        if (doc / rel).exists():
            problems.append(f'retired page still present: {rel}')
    if not problems:
        outside = len(sources) - len(expected & sources)
        print(f'API docs: all {len(expected)} pages of the {ROOT} closure present, '
              f'{len(SENTINELS)} sentinel declarations found, {len(RETIRED_PAGES)} retired '
              f'pages absent; {outside} source modules outside the documented inventory.')
    return problems


def self_test(src_root: pathlib.Path) -> None:
    with tempfile.TemporaryDirectory() as tmp:
        doc = pathlib.Path(tmp) / 'doc'
        for mod in closure(ROOT, src_root):
            page = doc / page_of(mod)
            page.parent.mkdir(parents=True, exist_ok=True)
            page.write_text('<html></html>')
        for rel, decl in SENTINELS:
            (doc / rel).write_text(f'<div id="{decl}"></div>')

        def expect(label: str, ok: bool) -> None:
            problems = check(doc, src_root)
            if bool(problems) == ok:
                sys.exit(f'self-test FAILED at "{label}": problems={problems}')
            print(f'self-test: {label}: {"pass" if ok else "fail"} as expected')

        expect('complete synthetic tree', True)
        rel, decl = SENTINELS[0]
        (doc / rel).write_text('<div id="something.else"></div>')
        expect('sentinel anchor removed', False)
        (doc / rel).write_text(f'<div id="{decl}"></div>')
        victim = doc / page_of('InfinitaryLogic.Descriptive.FragmentSpectrum')
        saved = victim.read_text()
        victim.unlink()
        expect('page removed', False)
        victim.write_text(saved)
        retired = doc / RETIRED_PAGES[0]
        retired.parent.mkdir(parents=True, exist_ok=True)
        retired.write_text('<html></html>')
        expect('retired page present', False)
        retired.unlink()
        expect('restored synthetic tree', True)
    print('self-test: OK')


def main() -> None:
    src_root = pathlib.Path(__file__).resolve().parent.parent
    if len(sys.argv) > 1 and sys.argv[1] == '--self-test':
        self_test(src_root)
        return
    doc = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else 'docbuild/.lake/build/doc')
    if not doc.is_dir():
        sys.exit(f'docs directory not found: {doc}')
    problems = check(doc, src_root)
    if problems:
        for p in problems:
            print('FAIL:', p)
        sys.exit(1)


if __name__ == '__main__':
    main()

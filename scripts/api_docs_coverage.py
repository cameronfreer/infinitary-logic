#!/usr/bin/env python3
"""Check that the generated API docs cover exactly the documented import closure.

doc-gen4 documents the transitive import closure of the default library's root module
(`InfinitaryLogic.lean`). This script recomputes that closure from `import` lines and asserts
that (a) every module in it has a generated HTML page and (b) no page exists for a module with no
source file. Run after `lake build InfinitaryLogic:docs` in `docbuild/`.

Not a `scripts/check_*` guard of the Lean build: it needs the generated docs, so the docs
workflow runs it explicitly.

Usage: python3 scripts/api_docs_coverage.py [DOC_DIR]   (default docbuild/.lake/build/doc)
"""
import pathlib
import re
import sys

ROOT = 'InfinitaryLogic'
IMPORT_RE = re.compile(r'^\s*import\s+(InfinitaryLogic(?:\.[A-Za-z0-9_]+)*)\s*$', re.M)


def module_path(mod: str) -> pathlib.Path:
    return pathlib.Path(*mod.split('.')).with_suffix('.lean')


def closure(root: str) -> set[str]:
    seen, todo = set(), [root]
    while todo:
        mod = todo.pop()
        if mod in seen:
            continue
        seen.add(mod)
        src = module_path(mod)
        if not src.exists():
            sys.exit(f'module {mod} imported but {src} does not exist')
        todo.extend(IMPORT_RE.findall(src.read_text()))
    return seen


def main() -> None:
    doc = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else 'docbuild/.lake/build/doc')
    expected = {m.replace('.', '/') for m in closure(ROOT)}
    pages = {p.relative_to(doc).with_suffix('').as_posix()
             for p in (doc / ROOT).rglob('*.html')}
    if (doc / f'{ROOT}.html').exists():
        pages.add(ROOT)
    sources = {p.with_suffix('').as_posix() for p in pathlib.Path(ROOT).rglob('*.lean')} | {ROOT}
    missing = sorted(expected - pages)
    stale = sorted(pages - sources)
    outside = sorted(sources - expected)
    if missing or stale:
        print('missing pages:', missing)
        print('pages without a source module:', stale)
        sys.exit(1)
    print(f'API docs cover all {len(expected)} modules of the {ROOT} import closure; '
          f'{len(outside)} source modules outside the documented closure (not expected).')


if __name__ == '__main__':
    main()

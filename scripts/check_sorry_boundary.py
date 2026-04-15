#!/usr/bin/env python3
"""Verify no syntactic `sorry` (or `sorryAx`) appears in code outside
`InfinitaryLogic/Conditional/`.

Strips Lean comments (line `--` and block `/- ... -/`, including the docstring
variants `/-- ... -/` and `/-! ... -/`) before searching, so docstring and
comment mentions of the word "sorry" are ignored and any code-position sorry
is caught regardless of syntactic shape.

Exit 0 if clean, 1 if any violation found.
"""
import os
import re
import sys

ROOTS = ["InfinitaryLogic.lean", "InfinitaryLogic"]
EXCLUDE_PREFIX = "InfinitaryLogic/Conditional/"

BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT = re.compile(r"--.*?$", re.MULTILINE)
SORRY = re.compile(r"\b(sorry|sorryAx)\b")


def targets():
    for root in ROOTS:
        if os.path.isfile(root) and root.endswith(".lean"):
            yield root
        elif os.path.isdir(root):
            for dirpath, _, files in os.walk(root):
                norm = dirpath.replace(os.sep, "/") + "/"
                if norm.startswith(EXCLUDE_PREFIX):
                    continue
                for f in files:
                    if f.endswith(".lean"):
                        yield os.path.join(dirpath, f)


def strip_comments(src: str) -> str:
    src = BLOCK_COMMENT.sub("", src)
    src = LINE_COMMENT.sub("", src)
    return src


def main() -> int:
    violations = []
    for path in targets():
        with open(path, "r", encoding="utf-8") as f:
            src = f.read()
        stripped = strip_comments(src)
        hits = SORRY.findall(stripped)
        if hits:
            violations.append((path, len(hits)))

    if violations:
        print("ERROR: 'sorry' (or 'sorryAx') found in code outside "
              "InfinitaryLogic/Conditional/:")
        for path, n in violations:
            print(f"  {path}: {n} occurrence(s)")
        return 1

    print("OK: no 'sorry' in code outside InfinitaryLogic/Conditional/")
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Verify no syntactic `sorry` (or `sorryAx`) appears in Lean code outside
the configured exempt regions.

Exempt regions are paths where in-progress frontier sorries are allowed:
- `InfinitaryLogic/Conditional/`: conditional results stratum.
- `InfinitaryLogic/Combinatorics/ErdosRado.lean`: active Erdős–Rado work
  region (named frontier sorries such as `extendToExt`,
  `exists_coherentMajorityBranch`, plus internal scaffolding).

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
# Paths exempt from the sorry-boundary check. Directories end with `/`;
# bare filenames match exactly.
EXCLUDE_PATHS = (
    "InfinitaryLogic/Conditional/",
    "InfinitaryLogic/Combinatorics/ErdosRado.lean",
)

BLOCK_COMMENT = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT = re.compile(r"--.*?$", re.MULTILINE)
SORRY = re.compile(r"\b(sorry|sorryAx)\b")


def is_exempt(path: str) -> bool:
    norm = path.replace(os.sep, "/")
    for excl in EXCLUDE_PATHS:
        if excl.endswith("/"):
            if norm.startswith(excl):
                return True
        else:
            if norm == excl:
                return True
    return False


def targets():
    for root in ROOTS:
        if os.path.isfile(root) and root.endswith(".lean"):
            if not is_exempt(root):
                yield root
        elif os.path.isdir(root):
            for dirpath, _, files in os.walk(root):
                for f in files:
                    if not f.endswith(".lean"):
                        continue
                    path = os.path.join(dirpath, f)
                    if not is_exempt(path):
                        yield path


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
        print("ERROR: 'sorry' (or 'sorryAx') found in non-exempt code:")
        for path, n in violations:
            print(f"  {path}: {n} occurrence(s)")
        print("Exempt paths:")
        for excl in EXCLUDE_PATHS:
            print(f"  {excl}")
        return 1

    print("OK: no 'sorry' in non-exempt code (exempt: "
          + ", ".join(EXCLUDE_PATHS) + ")")
    return 0


if __name__ == "__main__":
    sys.exit(main())

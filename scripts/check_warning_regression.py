#!/usr/bin/env python3
"""Fail if the build emits any warning that is not explicitly allowlisted.

The tree was swept to zero incidental warnings on 2026-08-24 (930 -> 5). This gate keeps it
there: a new warning is a build failure, not a line of scrollback nobody reads.

Usage:
    lake build <CI targets> 2>&1 | tee build.log
    python3 scripts/check_warning_regression.py build.log

With no argument the build is run here, using the same targets as
``.github/workflows/build.yml``. Passing a log avoids paying for the build twice in CI.

**The allowlist is deliberately narrow.** It matches on (file, substring of the message), not on
counts, so an allowlisted file cannot quietly accumulate unrelated warnings. Adding an entry means
asserting the warning is intended and permanent-ish; the sweep showed almost none are.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# Matches the build step of .github/workflows/build.yml.
TARGETS = [
    "InfinitaryLogic",
    "InfinitaryLogic.Everything",
    ":blueprint",
    ":blueprintJson",
    "InfinitaryLogicWIP",
]

# (file, message substring) pairs that are intentional and must not fail the gate.
#
# The issue #34 Henkin re-export shims are deprecated on purpose and imported by Everything.lean
# on purpose, so that CI keeps compiling them for the one release they are promised to survive.
# Everything.lean documents this at the import site. When they are finally deleted, delete these
# entries too — the gate will then prove no other consumer was relying on them.
ALLOWLIST: list[tuple[str, str]] = [
    ("InfinitaryLogic/Everything.lean", "InfinitaryLogic.Methods.Interpolation.GeneratedUniverse"),
    ("InfinitaryLogic/Everything.lean", "InfinitaryLogic.Methods.Interpolation.ConsistencyPropertyEqOn"),
    ("InfinitaryLogic/Everything.lean", "InfinitaryLogic.Methods.Interpolation.FairEnumeration"),
    ("InfinitaryLogic/Everything.lean", "InfinitaryLogic.Methods.Interpolation.QuotientTermModel"),
    ("InfinitaryLogic/Everything.lean", "InfinitaryLogic.Methods.Interpolation.QuotientTruthLemma"),
]

WARNING_RE = re.compile(r"^warning: ([^:]+\.lean):(\d+):(\d+): (.*)$")
# A diagnostic's continuation lines run until the next lake progress marker.
BOUNDARY = ("✔ ", "⚠ ", "ℹ ", "error:", "warning:", "info: ", "Build completed")


def parse(log: str) -> list[dict]:
    lines = log.split("\n")
    heads = [(i, m) for i, l in enumerate(lines) if (m := WARNING_RE.match(l))]
    out = []
    for k, (i, m) in enumerate(heads):
        end = heads[k + 1][0] if k + 1 < len(heads) else len(lines)
        body = [lines[i]]
        for j in range(i + 1, end):
            if lines[j].startswith(BOUNDARY):
                break
            body.append(lines[j])
        out.append(
            {
                "file": m.group(1),
                "line": int(m.group(2)),
                "col": int(m.group(3)),
                "text": "\n".join(body),
            }
        )
    return out


def allowed(w: dict) -> bool:
    return any(f == w["file"] and sub in w["text"] for f, sub in ALLOWLIST)


def main() -> int:
    if len(sys.argv) > 1:
        log = Path(sys.argv[1]).read_text()
    else:
        print(f"check_warning_regression: lake build {' '.join(TARGETS)}", flush=True)
        proc = subprocess.run(
            ["lake", "build", *TARGETS],
            cwd=REPO,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        log = proc.stdout
        if proc.returncode != 0:
            sys.stdout.write(log)
            print("FAIL: the build itself failed; warnings not assessed.")
            return 1

    warnings = parse(log)
    unexpected = [w for w in warnings if not allowed(w)]
    covered = len(warnings) - len(unexpected)

    if unexpected:
        print(f"FAIL: {len(unexpected)} unexpected warning(s).\n")
        for w in unexpected:
            print(w["text"])
            print()
        print(
            f"{len(unexpected)} unexpected, {covered} allowlisted.\n"
            "Fix the warning. Only add to ALLOWLIST if it is genuinely intended and you can say why."
        )
        return 1

    missing = [
        (f, sub)
        for f, sub in ALLOWLIST
        if not any(w["file"] == f and sub in w["text"] for w in warnings)
    ]
    if missing:
        # A stale allowlist is a silent hole: it would keep passing after the warning it excuses
        # is gone, and would then excuse a future warning that merely resembles it.
        print(f"FAIL: {len(missing)} allowlist entr(y/ies) matched nothing and are now stale:")
        for f, sub in missing:
            print(f"  {f}: {sub}")
        print("Remove them from ALLOWLIST.")
        return 1

    print(f"OK: no unexpected warnings ({covered} allowlisted, all still present).")
    return 0


if __name__ == "__main__":
    sys.exit(main())

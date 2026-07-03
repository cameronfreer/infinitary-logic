#!/usr/bin/env bash
# Guard the local EMContext stack's import boundary. `LocalEMContext.lean` is the pure local
# context machinery and must stay EM-free and Conditional-free: it may reach tail-indiscernibility
# ONLY through the neutral `Methods/TailIndiscernible.lean`, never through `Methods/EM/*`, the
# legacy `Methods/EMTermModel.lean`, or anything under `Conditional/`.
#
# `lake env lean --deps <file>` reports only DIRECT imports, so it cannot catch an indirect leak;
# this walks the transitive source-import closure instead.
set -euo pipefail
cd "$(dirname "$0")/.."

python3 - <<'PY'
import re, os, sys

def path_of(mod):
    p = mod.replace('.', '/') + '.lean'
    return p if os.path.exists(p) else None

root = "InfinitaryLogic.Methods.LocalEMContext"
seen, stack = set(), [root]
while stack:
    m = stack.pop()
    if m in seen:
        continue
    seen.add(m)
    p = path_of(m)
    if not p:
        continue
    with open(p) as f:
        for line in f:
            mm = re.match(r'\s*import\s+(InfinitaryLogic\S+)', line)
            if mm:
                stack.append(mm.group(1).strip())

bad = [m for m in sorted(seen)
       if '.Conditional.' in m or m.endswith('.Conditional')
       or '.Methods.EM.' in m or m.endswith('.Methods.EMTermModel')]
if bad:
    print("ERROR: the pure local context " + root + " transitively imports")
    print("EM/Conditional modules (it must reach tail-indiscernibility only via")
    print("Methods/TailIndiscernible):")
    for m in bad:
        print("  " + m)
    sys.exit(1)
if "InfinitaryLogic.Methods.TailIndiscernible" not in seen:
    print("ERROR: " + root + " does not reach Methods/TailIndiscernible")
    sys.exit(1)
print("OK: " + root + " transitive closure (" + str(len(seen))
      + " modules) is EM-free and Conditional-free.")
PY

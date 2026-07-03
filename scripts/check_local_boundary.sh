#!/usr/bin/env bash
# Guard the pure local EMContext/EMTruth stack's import boundary. `LocalEMContext.lean` (the
# quotient/structure machinery) and `LocalEMTruth.lean` (the Skolem-witness transport) must stay
# EM-free and Conditional-free: they may reach tail-indiscernibility ONLY through the neutral
# `Methods/TailIndiscernible.lean`, never through `Methods/EM/*`, the legacy
# `Methods/EMTermModel.lean`, or anything under `Conditional/`.
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

roots = ["InfinitaryLogic.Methods.LocalEMContext", "InfinitaryLogic.Methods.LocalEMTruth"]

def closure(root):
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
    return seen

failed = False
for root in roots:
    seen = closure(root)
    bad = [m for m in sorted(seen)
           if '.Conditional.' in m or m.endswith('.Conditional')
           or '.Methods.EM.' in m or m.endswith('.Methods.EMTermModel')]
    if bad:
        failed = True
        print("ERROR: the pure local module " + root + " transitively imports")
        print("EM/Conditional modules (it must reach tail-indiscernibility only via")
        print("Methods/TailIndiscernible):")
        for m in bad:
            print("  " + m)
        continue
    if "InfinitaryLogic.Methods.TailIndiscernible" not in seen:
        failed = True
        print("ERROR: " + root + " does not reach Methods/TailIndiscernible")
        continue
    print("OK: " + root + " transitive closure (" + str(len(seen))
          + " modules) is EM-free and Conditional-free.")
if failed:
    sys.exit(1)
PY

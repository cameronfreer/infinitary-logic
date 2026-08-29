#!/usr/bin/env bash
# Every post-build guard, in ONE place, so the local gate and CI cannot drift apart.
#
# Why this exists: `build_gate.sh` promised "the build or any guard" while running only the
# sorry boundary and the warning regression. The Lean cone guards, the headline-axiom scan and
# the blueprint declaration check ran in CI alone. A rename that broke
# `check_admissible_surface.lean` therefore passed the local gate and would have failed CI.
#
# The anti-drift property is a single DISCOVERY RULE, not a single list: every
# `scripts/check_*.{lean,py,sh}` is picked up automatically, so a new guard needs no edit here.
# Resist replacing it with an allowlist, and resist quoting a count of guards anywhere — the
# count changes and the prose goes stale, which is the failure mode this file exists to stop.
#
# One check is NOT discovered and stays explicit: `lake exe checkdecls`, which is a lake
# executable rather than a `scripts/check_*` file.
#
# Assumes `lake build` has already succeeded — run it via `build_gate.sh`, or after a build.
set -euo pipefail
cd "$(dirname "$0")/.."

self="$(basename "$0")"
failed=()

run() {
  echo "── $*"
  if ! "$@"; then failed+=("$*"); fi
}

# Python and shell guards (excluding this runner, which would recurse).
for f in scripts/check_*.py; do
  [ -e "$f" ] || continue
  run python3 "$f"
done
for f in scripts/check_*.sh; do
  [ -e "$f" ] || continue
  [ "$(basename "$f")" = "$self" ] && continue
  run bash "$f"
done

# Blueprint declaration names must still resolve.
run lake exe checkdecls blueprint/lean_decls

# Lean cone / surface guards. `lake env lean` exits 0 on `logInfo` and nonzero on `throwError`.
for f in scripts/check_*.lean; do
  [ -e "$f" ] || continue
  run lake env lean "$f"
done

if [ ${#failed[@]} -ne 0 ]; then
  echo
  echo "check_all_guards: FAILED (${#failed[@]}):"
  printf '  %s\n' "${failed[@]}"
  exit 1
fi
echo "check_all_guards: OK"

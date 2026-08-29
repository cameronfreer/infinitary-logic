#!/usr/bin/env bash
# Every post-build guard, in ONE place, so the local gate and CI cannot drift apart.
#
# Why this exists: `build_gate.sh` promised "the build or any guard" while running only the
# sorry boundary and the warning regression. Six Lean cone guards, the headline-axiom scan and
# the blueprint declaration check ran in CI alone. A rename that broke
# `check_admissible_surface.lean` therefore passed the local gate and would have failed CI.
#
# Guards are DISCOVERED by glob, not listed. A new `scripts/check_*.{lean,py,sh}` is picked up
# automatically; there is no second list to forget to update. That is the whole anti-drift
# property, so resist adding an explicit allowlist here.
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

#!/usr/bin/env bash
# Guard the headline declarations: (1) the default import surface
# (`import InfinitaryLogic`) must expose the Morley-Hanf endpoints, and
# (2) every headline declaration must depend on exactly the standard axioms
# [propext, Classical.choice, Quot.sound] (subsets allowed) - in particular
# no sorryAx and no custom axioms.
set -euo pipefail
cd "$(dirname "$0")/.."

TMPDIR="$(mktemp -d)"
trap 'rm -rf "$TMPDIR"' EXIT

# Headline declarations on the DEFAULT surface (import InfinitaryLogic).
cat > "$TMPDIR/default.lean" <<'EOF'
import InfinitaryLogic
#print axioms FirstOrder.Language.morley_hanf
#print axioms FirstOrder.Language.morleySeedTailTemplateRealizable_holds
#print axioms FirstOrder.Language.hanfNumber_le_beth_omega1
#print axioms FirstOrder.Language.Lomega1omegaHanfNumber_le_beth_omega1
#print axioms FirstOrder.Language.Lomega1omegaHanfNumber_eq_beth_omega1
#print axioms FirstOrder.Language.exists_small_model_of_hasArbLargeModels
#print axioms FirstOrder.Language.exists_complete_sentence_of_lomega1omegaSmall
#print axioms FirstOrder.Language.exists_complete_kCategorical_of_hasArbLargeModels
#print axioms FirstOrder.Language.morley_hanf_theory
#print axioms FirstOrder.Language.karp_theorem_w
#print axioms FirstOrder.Language.model_existence
#print axioms FirstOrder.Language.craig_interpolation
EOF

# Headline declarations that live in the Everything closure.
cat > "$TMPDIR/everything.lean" <<'EOF'
import InfinitaryLogic.Everything
#print axioms gandy_harrington_for_relation
#print axioms FirstOrder.Language.silverBurgessDichotomy
EOF

check_file () {
  local out
  out="$(lake env lean "$1")" || {
    echo "FAIL: $1 did not elaborate (declaration missing from surface?)" >&2
    exit 1
  }
  echo "$out"
  # Every axiom list must be a subset of the standard three.
  local bad
  bad="$(echo "$out" | grep -o '\[[^]]*\]' \
    | tr -d '[]' | tr ',' '\n' | tr -d ' ' \
    | grep -v -E '^(propext|Classical\.choice|Quot\.sound)$' || true)"
  if [ -n "$bad" ]; then
    echo "FAIL: non-standard axioms detected: $bad" >&2
    exit 1
  fi
}

check_file "$TMPDIR/default.lean"
check_file "$TMPDIR/everything.lean"
echo "OK: headline declarations exposed and standard-axiom-clean."

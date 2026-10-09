#!/usr/bin/env bash
# Guard the headline declarations: (1) the default import surface
# (`import InfinitaryLogic`) must expose the Morley-Hanf endpoints and the other default
# headlines, and (2) every headline declaration must depend on exactly the standard axioms
# [propext, Classical.choice, Quot.sound] (subsets allowed) - in particular no sorryAx and no
# custom axioms.
#
# The check is STRUCTURAL: `scripts/check_headline_axioms.lean` resolves each listed name in the
# environment, checks default-surface membership through the import closure, runs
# `Lean.collectAxioms`, requires complete coverage, and first checks two negative controls
# (a sorry-proved and a custom-axiom declaration must both be flagged). The previous version
# parsed the printed `#print axioms` output line by line and skipped every axiom list that
# Lean wrapped across lines. The headline name lists live in that Lean file.
set -euo pipefail
cd "$(dirname "$0")/.."

lake env lean scripts/check_headline_axioms.lean || {
  echo "FAIL: scripts/check_headline_axioms.lean reported a headline-axiom violation" >&2
  exit 1
}
echo "OK: headline declarations exposed and standard-axiom-clean."

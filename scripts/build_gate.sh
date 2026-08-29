#!/usr/bin/env bash
# The checked build gate: run before ANY commit that touches Lean files.
# Exits nonzero if the build or any guard fails — safe to chain with &&.
# The guard list lives in scripts/check_all_guards.sh, which CI invokes too, so the local
# gate and CI cannot drift. Do not add individual guards here.
# Never pipe `lake build` through tail/grep without this wrapper: a successful
# pipe tail must not certify a failed build (incident: commit 27145eb).
set -euo pipefail
cd "$(dirname "$0")/.."
# Default targets must match .github/workflows/build.yml, or the gate passes on a
# strictly smaller module set than CI checks. `InfinitaryLogic` alone does NOT reach
# `InfinitaryLogic/Conditional/`; only `Everything` does (incident: a new Conditional
# module compiled nowhere while this gate reported OK).
# An array, not a string: `targets="${@:-...}"` collapses the positional parameters into one
# scalar, so a target containing whitespace would be re-split and an empty one silently dropped.
if (( $# )); then
  targets=("$@")
else
  targets=(InfinitaryLogic InfinitaryLogic.Everything InfinitaryLogicWIP)
fi
echo "build_gate: lake build ${targets[*]}"
lake build "${targets[@]}"
bash scripts/check_all_guards.sh
echo "build_gate: OK"

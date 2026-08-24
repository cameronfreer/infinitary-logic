#!/usr/bin/env bash
# The checked build gate: run before ANY commit that touches Lean files.
# Exits nonzero if the build or any guard fails — safe to chain with &&.
# Never pipe `lake build` through tail/grep without this wrapper: a successful
# pipe tail must not certify a failed build (incident: commit 27145eb).
set -euo pipefail
cd "$(dirname "$0")/.."
# Default targets must match .github/workflows/build.yml, or the gate passes on a
# strictly smaller module set than CI checks. `InfinitaryLogic` alone does NOT reach
# `InfinitaryLogic/Conditional/`; only `Everything` does (incident: a new Conditional
# module compiled nowhere while this gate reported OK).
targets="${@:-InfinitaryLogic InfinitaryLogic.Everything InfinitaryLogicWIP}"
echo "build_gate: lake build $targets"
lake build $targets
python3 scripts/check_sorry_boundary.py
python3 scripts/check_warning_regression.py
echo "build_gate: OK"

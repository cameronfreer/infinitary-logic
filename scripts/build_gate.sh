#!/usr/bin/env bash
# The checked build gate: run before ANY commit that touches Lean files.
# Exits nonzero if the build or any guard fails — safe to chain with &&.
# Never pipe `lake build` through tail/grep without this wrapper: a successful
# pipe tail must not certify a failed build (incident: commit 27145eb).
set -euo pipefail
cd "$(dirname "$0")/.."
targets="${@:-InfinitaryLogic InfinitaryLogicWIP}"
echo "build_gate: lake build $targets"
lake build $targets
python3 scripts/check_sorry_boundary.py
echo "build_gate: OK"

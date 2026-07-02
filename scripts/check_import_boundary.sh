#!/usr/bin/env bash
# Guard the import boundary: the default (sorry-free) surface must not
# transitively import the sorry-exempt legacy ErdosRado module. The
# source-level sorry check (check_sorry_boundary.py) cannot catch a
# re-import of an exempt file, so this asserts it at the import graph.
set -euo pipefail
cd "$(dirname "$0")/.."

deps=$(lake env lean --deps InfinitaryLogic.lean)
if hits=$(echo "$deps" | grep 'ErdosRado'); then
  echo "ERROR: the default surface (InfinitaryLogic.lean) transitively imports"
  echo "the legacy sorry-exempt ErdosRado module (should be Everything-only):"
  echo "$hits"
  exit 1
fi
echo "OK: default surface does not import ErdosRado."

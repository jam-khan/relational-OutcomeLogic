#!/usr/bin/env bash
# Gate: full build, no sorry/admit, standard axioms only.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build

if grep -rn --include='*.lean' -E '\bsorry\b|\badmit\b' RelationalOutcomeLogic/ RelationalOutcomeLogic.lean; then
  echo "FAIL: sorry/admit found" >&2
  exit 1
fi
lake env lean scripts/AxiomGate.lean
echo "OK: build green, no sorries, standard axioms only"

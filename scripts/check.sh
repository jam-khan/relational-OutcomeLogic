#!/usr/bin/env bash
# Gate: source structure, full build, no sorry/admit, standard axioms only.
set -euo pipefail
cd "$(dirname "$0")/.."

python3 scripts/check-structure.py
lake build

if grep -rn --include='*.lean' -E '\bsorry\b|\badmit\b' RelationalOutcomeLogic/ RelationalOutcomeLogic.lean; then
  echo "FAIL: sorry/admit found" >&2
  exit 1
fi
lake env lean scripts/AxiomGate.lean
echo "OK: source structure checked, build green, no sorries, standard axioms only"

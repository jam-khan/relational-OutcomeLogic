#!/usr/bin/env bash
# Gate: full build + no sorry/admit anywhere in the library.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build

if grep -rn --include='*.lean' -E '\bsorry\b|\badmit\b' RelationalOutcomeLogic/ RelationalOutcomeLogic.lean; then
  echo "FAIL: sorry/admit found" >&2
  exit 1
fi
echo "OK: build green, no sorries"

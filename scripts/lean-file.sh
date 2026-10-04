#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ -f ./env.sh ]]; then source ./env.sh; fi
module="${1%.lean}"
mkdir -p ".lake/build/lib/lean/$(dirname "$module")"
if [[ -n "${CELL_LEAN_BIN:-}" ]]; then
  "$CELL_LEAN_BIN" -o ".lake/build/lib/lean/$module.olean" -i ".lake/build/lib/lean/$module.ilean" "$module.lean"
else
  lake env lean -o ".lake/build/lib/lean/$module.olean" -i ".lake/build/lib/lean/$module.ilean" "$module.lean"
fi

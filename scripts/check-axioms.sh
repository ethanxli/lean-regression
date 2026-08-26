#!/usr/bin/env bash
set -euo pipefail

certificate="docs/AXIOMS.txt"
actual="$(mktemp)"
trap 'rm -f "$actual"' EXIT

NO_COLOR=1 lake env lean AxiomAudit.lean > "$actual"

if grep -Eq 'sorryAx|Lean\.ofReduceBool' "$actual"; then
  echo "The axiom audit contains a forbidden trust escape hatch." >&2
  grep -E 'sorryAx|Lean\.ofReduceBool' "$actual" >&2
  exit 1
fi

diff -u "$certificate" "$actual"

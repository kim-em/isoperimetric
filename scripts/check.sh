#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
lake env lean AxiomAudit.lean
# These checks apply to local mathematical sources, not unused benchmark templates.
if rg -n '\b(sorry|admit|axiom|native_decide)\b' Isoperimetric.lean Isoperimetric; then
  echo 'Forbidden proof placeholder or bypass in local mathematical sources.' >&2
  exit 1
fi

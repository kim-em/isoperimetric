#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
lake env lean -DwarningAsError=true -Dlinter.mathlibStandardSet=true AxiomAudit.lean
lake env lean -DwarningAsError=true -Dlinter.mathlibStandardSet=true StatementCheck.lean
# These checks apply to local mathematical sources, not unused benchmark templates.
# grep is present on the CI runner. Only exit 1 means a successful scan with no matches;
# a missing command or unreadable input must fail verification.
scan_status=0
grep -Enr '(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide)([^[:alnum:]_]|$)|debug\.skipKernelTC' \
  Isoperimetric.lean Isoperimetric StatementCheck.lean || scan_status=$?
case "$scan_status" in
  0)
    echo 'Forbidden proof placeholder or bypass in local mathematical sources.' >&2
    exit 1
    ;;
  1) ;;
  *)
    echo "Source scan failed with exit status $scan_status." >&2
    exit "$scan_status"
    ;;
esac

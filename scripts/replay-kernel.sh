#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Export precisely the final declarations and all of their proof dependencies.
# Replaying this export starts from an empty kernel environment, without trusting
# imported .olean declarations or checking unrelated imported mathematics.
replay_dir=$(mktemp -d "${TMPDIR:-/tmp}/isoperimetric-replay.XXXXXX")
trap 'rm -f "$replay_dir/proof.ndjson"; rmdir "$replay_dir"' EXIT
lake env leanexport Isoperimetric.Main -- \
  Isoperimetric.classical_isoperimetric \
  Isoperimetric.classical_isoperimetric_specification \
  Isoperimetric.RectifiableJordan.equality_of_circle > "$replay_dir/proof.ndjson"
lake env leanchecker --from-export "$replay_dir/proof.ndjson"

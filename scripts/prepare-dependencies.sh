#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

archive=.lake/packages/isoperimetric_inequality
expected=6a6d9f67a91d546677321aeea559c2857b697635
# Hugging Face advertises Git partial clone support, but fetching individual
# promised blobs returns HTTP 500. Materialize this dependency without filters
# before Lake resolves the committed manifest. It remains a pinned Git package.
if [[ ! -d "$archive/.git" ]]; then
  mkdir -p .lake/packages
  git clone https://huggingface.co/datasets/humanfia-lab/lean-eval-source "$archive"
  git -C "$archive" checkout "$expected"
fi
# Lake materializes the other committed pins and obtains Mathlib's compiled cache.
lake exe cache get
actual=$(git -C "$archive" rev-parse HEAD)
if [[ "$actual" != "$expected" ]]; then
  echo "Unexpected Humanfia revision: $actual" >&2
  exit 1
fi
patch="$PWD/patches/humanfia-lean-4.35.patch"
if git -C "$archive" apply --reverse --check "$patch" 2>/dev/null; then
  echo 'Humanfia compatibility patch is already applied.'
else
  git -C "$archive" apply --check "$patch"
  git -C "$archive" apply "$patch"
  echo 'Applied Humanfia compatibility patch.'
fi

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
# Apply the library-ownership patch before Lake reads MovingSofa's configuration.
# Its vendored TauCeti library must not overlap the upstream TauCeti package.
sofa=.lake/packages/MovingSofa
sofa_expected=4d5569131940815f47a9ccf3e90a4c5043c56127
if [[ ! -d "$sofa/.git" ]]; then
  git clone https://github.com/deancureton/MovingSofa.git "$sofa"
  git -C "$sofa" checkout "$sofa_expected"
fi
sofa_actual=$(git -C "$sofa" rev-parse HEAD)
if [[ "$sofa_actual" != "$sofa_expected" ]]; then
  echo "Unexpected MovingSofa revision: $sofa_actual" >&2
  exit 1
fi
sofa_patch="$PWD/patches/movingsofa-upstream-tauceti.patch"
if git -C "$sofa" apply --reverse --check "$sofa_patch" 2>/dev/null; then
  echo 'MovingSofa library-ownership patch is already applied.'
else
  git -C "$sofa" apply --check "$sofa_patch"
  git -C "$sofa" apply "$sofa_patch"
  echo 'Applied MovingSofa library-ownership patch.'
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

#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel 2>/dev/null)" || {
  echo "extraction provenance requires a Git checkout" >&2
  exit 1
}

extraction_inputs=(
  theories/dune
  theories/dune-project
  theories/extraction/dune
  theories/extraction/patch_extraction.sh
  theories/extraction/resolve_source_commit.sh
  theories/extraction/run_extraction.sh
  theories/extraction/source_commit.sh
  theories/extract/extraction_header.txt
  ':(glob)theories/**/*.v'
)

if ! git -C "$repo_root" diff --quiet -- "${extraction_inputs[@]}" ||
   ! git -C "$repo_root" diff --cached --quiet -- "${extraction_inputs[@]}"; then
  echo "extraction inputs have uncommitted changes; commit them before regenerating" >&2
  exit 1
fi

untracked_inputs="$(
  git -C "$repo_root" ls-files --others --exclude-standard -- \
    ':(glob)theories/**/*.v'
)"
if [ -n "$untracked_inputs" ]; then
  echo "untracked Rocq sources must be committed before regenerating:" >&2
  printf '%s\n' "$untracked_inputs" >&2
  exit 1
fi

source_commit="$(
  git -C "$repo_root" log --no-merges -1 --format=%H -- \
    "${extraction_inputs[@]}"
)"
if [[ ! "$source_commit" =~ ^[0-9a-f]{40}$ ]]; then
  echo "could not determine the committed extraction-input revision" >&2
  exit 1
fi

printf '%s' "$source_commit"

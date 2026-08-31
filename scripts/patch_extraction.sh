#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
source_commit="$("$repo_root/theories/extraction/source_commit.sh")"

QASMINFER_SOURCE_COMMIT="$source_commit" \
QASMINFER_DUNE_PROJECT="$repo_root/theories/dune-project" \
  exec "$repo_root/theories/extraction/patch_extraction.sh" "$@"

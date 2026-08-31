#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$script_dir/.." && pwd)"
source_commit="$("$repo_root/theories/extraction/source_commit.sh")"
rocq_version="$(rocq --print-version | awk 'NR == 1 { print $1 }')"
extraction_command="$(
  "$repo_root/theories/extraction/run_extraction.sh" --print-command
)"

QASMINFER_SOURCE_COMMIT="$source_commit" \
QASMINFER_ROCQ_VERSION="$rocq_version" \
QASMINFER_EXTRACTION_COMMAND="$extraction_command" \
QASMINFER_DUNE_PROJECT="$repo_root/theories/dune-project" \
  exec "$repo_root/theories/extraction/patch_extraction.sh" "$@"

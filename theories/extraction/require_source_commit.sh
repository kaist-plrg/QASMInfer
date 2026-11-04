#!/usr/bin/env bash
set -euo pipefail

source_commit="${QASMINFER_SOURCE_COMMIT:-}"

if [[ ! "$source_commit" =~ ^[0-9a-f]{40}$ ]]; then
  echo 'QASMINFER_SOURCE_COMMIT is required; compute it with theories/extraction/source_commit.sh before running the extraction alias' >&2
  exit 1
fi

printf '%s' "$source_commit"

#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo "usage: resolve_source_commit.sh <committed-extraction>" >&2
  exit 1
fi

committed_extraction="$1"
source_commit="${QASMINFER_SOURCE_COMMIT:-}"

if [ -z "$source_commit" ] && [ -f "$committed_extraction" ]; then
  source_commit="$(
    sed -n 's/^ \* Source commit: \([0-9a-f][0-9a-f]*\)$/\1/p' \
      "$committed_extraction"
  )"
fi

if [[ ! "$source_commit" =~ ^[0-9a-f]{40}$ ]]; then
  echo "could not resolve extraction source commit; regenerate with QASMINFER_SOURCE_COMMIT set" >&2
  exit 1
fi

printf '%s' "$source_commit"

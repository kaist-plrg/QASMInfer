#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 2 ]; then
  echo "usage: patch_extraction.sh <header-file> <generated-file>" >&2
  exit 1
fi

header="$1"
target="$2"

if [ ! -f "$header" ]; then
  echo "missing header $header" >&2
  exit 1
fi

if [ ! -f "$target" ]; then
  echo "missing generated file $target" >&2
  exit 1
fi

tmp="$(mktemp "${TMPDIR:-/tmp}/extracted.XXXXXX")"
cat "$header" "$target" > "$tmp"
mv "$tmp" "$target"

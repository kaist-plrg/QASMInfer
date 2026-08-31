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

source_commit="${QASMINFER_SOURCE_COMMIT:-}"
rocq_version="${QASMINFER_ROCQ_VERSION:-}"
extraction_command="${QASMINFER_EXTRACTION_COMMAND:-}"
dune_project="${QASMINFER_DUNE_PROJECT:-}"

if [[ ! "$source_commit" =~ ^[0-9a-f]{40}$ ]] ||
   [ -z "$rocq_version" ] ||
   [ -z "$extraction_command" ] ||
   [ ! -f "$dune_project" ]; then
  echo "missing or invalid extraction provenance environment" >&2
  exit 1
fi

dune_rocq_language_version="$(
  sed -n 's/^[[:space:]]*(using rocq \([^)]*\))[[:space:]]*$/\1/p' \
    "$dune_project"
)"
if [[ ! "$dune_rocq_language_version" =~ ^[0-9]+\.[0-9]+$ ]]; then
  echo "missing or invalid Dune Rocq language version in $dune_project" >&2
  exit 1
fi

case "$rocq_version$dune_rocq_language_version$extraction_command" in
  *'|'* | *'&'* | *'\'*)
    echo "unsupported character in extraction provenance" >&2
    exit 1
    ;;
esac

rendered_header="$(mktemp "${TMPDIR:-/tmp}/extraction-header.XXXXXX")"
patched_target="$(mktemp "${TMPDIR:-/tmp}/extracted.XXXXXX")"
cleanup() {
  rm -f "$rendered_header" "$patched_target"
}
trap cleanup EXIT

sed \
  -e "s|@SOURCE_COMMIT@|$source_commit|g" \
  -e "s|@ROCQ_VERSION@|$rocq_version|g" \
  -e "s|@DUNE_ROCQ_LANGUAGE_VERSION@|$dune_rocq_language_version|g" \
  -e "s|@EXTRACTION_COMMAND@|$extraction_command|g" \
  "$header" > "$rendered_header"

if grep -Eq '@(SOURCE_COMMIT|ROCQ_VERSION|DUNE_ROCQ_LANGUAGE_VERSION|EXTRACTION_COMMAND)@' \
  "$rendered_header"; then
  echo "unexpanded extraction provenance placeholder" >&2
  exit 1
fi

cat "$rendered_header" "$target" > "$patched_target"
mv "$patched_target" "$target"

#!/usr/bin/env bash
set -euo pipefail

extraction_args=(
  repl
  -q
  -Q
  ../..
  QASMInfer
  -batch
  -l
  ../../extract/Extract
)

case "${1:-}" in
  --print-command)
    if [ "$#" -ne 1 ]; then
      echo "usage: run_extraction.sh --print-command" >&2
      exit 1
    fi
    printf 'rocq'
    printf ' %s' "${extraction_args[@]}"
    ;;
  --run)
    if [ "$#" -ne 2 ]; then
      echo "usage: run_extraction.sh --run <rocq-binary>" >&2
      exit 1
    fi
    exec "$2" "${extraction_args[@]}"
    ;;
  *)
    echo "usage: run_extraction.sh --print-command | --run <rocq-binary>" >&2
    exit 1
    ;;
esac

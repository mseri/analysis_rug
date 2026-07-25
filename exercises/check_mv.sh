#!/bin/sh
# Check a Waterproof notebook (.mv) with fcc.
#
# The dual -R entries of ./_CoqProject confuse fcc (it looks for .vo files next
# to the sources), so we point it directly at the dune-built .vo files.
# Run `dune build` first.
#
# Usage: exercises/check_mv.sh exercises/solutions/hw2_series_ratio_solution.mv
set -e
cd "$(dirname "$0")/.."
for f in "$@"; do
  echo "== $f"
  fcc -R _build/default/theories,RUG.Analysis "$f" > /dev/null 2>&1 || true
  d="${f%.*}.diags"
  if [ -s "$d" ] && grep -q '"severity": 1' "$d"; then
    grep -A6 '"severity": 1' "$d" | grep '"message"' | cut -c1-200
    echo "   ^ errors above"
  else
    echo "   ok"
  fi
done

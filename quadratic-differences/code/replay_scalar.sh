#!/bin/sh
# Supply paths to the pinned Kissat executable and the independent DRAT checker.
set -eu
solver=${1:?supply the Kissat executable}
checker=${2:?supply the drat-trim executable}
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
for p in 10 11 12 13 14 15; do
    case $p in
        10|12|14) set -- --columns ;;
        *) set -- ;;
    esac
    python3 strip.py cnf "$p" 1 "$@" > "$out/graph.cnf"
    result=0
    "$solver" "$out/graph.cnf" "$out/graph.drat" > "$out/solver.log" || result=$?
    [ "$result" -eq 20 ]
    "$checker" "$out/graph.cnf" "$out/graph.drat" > "$out/check.log"
    tr '\r' '\n' < "$out/check.log" | grep -Fx 's VERIFIED'
    printf 'p=%s\n' "$p"
    sha256sum "$out/graph.cnf" "$out/graph.drat"
    rm "$out/graph.drat"
done

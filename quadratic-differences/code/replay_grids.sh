#!/bin/sh
# Run from the problem directory. Supply paths to Kissat 4.0.4 and drat-trim.
set -eu
kissat=${1:?supply the Kissat executable}
checker=${2:?supply the drat-trim executable}
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
for graph in rectangle crop; do
    if [ "$graph" = rectangle ]; then
        python3 encode.py grid 11 65 --parity 0 > "$out/graph.cnf"
        digest=28b969e5f4669bfc7a5a3ac5cab132d347afda1fe96cc456dce92307bccf9a83
    else
        python3 encode.py crop > "$out/graph.cnf"
        digest=4d7a888d0c668c6f11e44ad3af3bf912e3d67ea095d2e148d33707c7bc1e4a10
    fi
    printf '%s  %s\n' "$digest" "$out/graph.cnf" | sha256sum -c -
    result=0
    "$kissat" "$out/graph.cnf" "$out/graph.drat" > "$out/solver.log" || result=$?
    [ "$result" -eq 20 ]
    "$checker" "$out/graph.cnf" "$out/graph.drat" > "$out/check.log"
    tr '\r' '\n' < "$out/check.log" | grep -Fx 's VERIFIED'
    printf '%s: ' "$graph"
    sha256sum "$out/graph.drat"
    rm "$out/graph.drat"
done

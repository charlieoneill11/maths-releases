#!/bin/sh
# Run from the problem folder with the path of the compiled drat-trim checker.
set -eu
checker=${1:?supply the drat-trim executable}
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export PYTHONDONTWRITEBYTECODE=1
python3 forcing.py cnf 12 58 > "$out/input.cnf"
python3 audit_forcing.py "$out/input.cnf"
printf '%s  %s\n' 0e39e712bfba5a99cb880ded1c66fcfbc175b60b199e48bc432241d31fe28832 "$out/input.cnf" | sha256sum -c -
printf '%s  %s\n' 41e5c90b89a72038ab9d551a98752e369b01b6985679e7f1e8934d0738ada6f3 certificates/near-axis.drat.xz | sha256sum -c -
xz -dc certificates/near-axis.drat.xz > "$out/proof.drat"
printf '%s  %s\n' 1b8b8f21348fd5c06d508b157a49feb5881daf203c6ba1c08391e9c3a1ab6829 "$out/proof.drat" | sha256sum -c -
"$checker" "$out/input.cnf" "$out/proof.drat" > "$out/check.log"
tr '\r' '\n' < "$out/check.log" | grep -Fx 's VERIFIED'

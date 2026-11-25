#!/bin/sh
set -eu

side=${1:-}
case "$side" in
    85|133|141|205|261|301|cutoff|1445) ;;
    *) echo 'usage: sh replay.sh {85|133|141|205|261|301|cutoff|1445}' >&2; exit 2 ;;
esac

cd "$(dirname "$0")"
scratch=$(mktemp -d "${TMPDIR:-/tmp}/cube-${side}.XXXXXXXX")
echo "Replay files: $scratch"

if [ "$side" = cutoff ]; then
    "${CXX:-c++}" -std=c++17 -O3 cutoff_check.cpp -o "$scratch/cutoff"
    exec "$scratch/cutoff"
fi
if [ "$side" = 261 ] || [ "$side" = 301 ]; then
    python3 enumerate_85.py --side "$side" --homogeneous --output "$scratch/planes.bin"
    "${CXX:-c++}" -std=c++17 -O3 "-DPACKING_SIDE=$side" filter_85.cpp -o "$scratch/filter"
    "$scratch/filter" "$scratch/planes.bin" "$scratch/final.bin" --homogeneous
    test ! -s "$scratch/final.bin"
    exit
fi
if [ "$side" = 1445 ]; then
    "${CXX:-c++}" -std=c++17 -O3 verify_1445.cpp -o "$scratch/overlap"
    exec "$scratch/overlap"
fi

python3 enumerate_85.py --side "$side" --output "$scratch/planes.bin"
"${CXX:-c++}" -std=c++17 -O3 "-DPACKING_SIDE=$side" filter_85.cpp -o "$scratch/filter"
if [ "$side" != 141 ]; then
    "${CXX:-c++}" -std=c++17 -O3 "-DPACKING_SIDE=$side" verify_85_surgery.cpp -o "$scratch/surgery"
fi
case "$side" in
    85)
        "$scratch/surgery" "$scratch/planes.bin" "$scratch/remaining.bin"
        "$scratch/filter" "$scratch/remaining.bin" "$scratch/final.bin"
        ;;
    133|205)
        "$scratch/filter" "$scratch/planes.bin" "$scratch/remaining.bin"
        "$scratch/surgery" "$scratch/remaining.bin" "$scratch/final.bin"
        ;;
    141)
        "$scratch/filter" "$scratch/planes.bin" "$scratch/final.bin"
        ;;
esac

test -f "$scratch/final.bin" && test ! -s "$scratch/final.bin"

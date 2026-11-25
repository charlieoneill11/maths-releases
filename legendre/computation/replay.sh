#!/usr/bin/env bash
# Independent replay of every archived production, pilot and recovered regression interval.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
cd "$here"
export PYTHONDONTWRITEBYTECODE=1
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
cxx=${CXX:-c++}
"$cxx" -O2 -std=c++17 direct/interval_witness_codec.cpp -o "$build/interval_witness_codec"
"$cxx" -O2 -std=c++17 -DUSE_GMP direct/check_power_witnesses.cpp -lgmpxx -lgmp -o "$build/check_power_witnesses"
"$cxx" -O2 -std=c++17 -DPOWER_WITNESS_SQUARES direct/interval_witness_codec.cpp -o "$build/square_codec"
"$cxx" -O2 -std=c++17 -DPOWER_WITNESS_SQUARES -DUSE_GMP direct/check_power_witnesses.cpp -lgmpxx -lgmp -o "$build/square_verify"
for shard in direct/sealed/*.iw.gz direct/continuation/*.iw.gz; do
    name="${shard##*/}"
    range="${name%.iw.gz}"
    gzip -dc "$shard" | "$build/interval_witness_codec" unpack | "$build/check_power_witnesses" "${range%-*}" "${range#*-}"
done
while read -r name first last; do
    gzip -dc "squares/$name.iw.gz" | "$build/square_codec" unpack | "$build/square_verify" "$first" "$last"
done <<'RANGES'
low 70500001100001 70500002100000
midpoint85 85249999000001 85250000000000
target100 99999999000001 100000000000000
high 733395927758894 733395928758893
RANGES
python3 squares/check_square_witnesses.py 70500000000001 70500001000000 squares/square_witnesses.gz
python3 squares/check_square_witnesses.py 70500001000001 70500001100000 squares/square_oppermann_extension.gz
python3 -S direct/power_pilot_certificates.py 32654578782390 32654578784437 cloud/gce_local_smoke/two_worker/sample.iw.gz
python3 -S direct/power_pilot_certificates.py 32654578787038 32654578787041 cloud/gce_local_smoke/worker_matrix/sample.iw.gz
for cert in direct/examples/pratt-fallback-*.json; do
    name="${cert##*/}"
    base="${name#pratt-fallback-}"
    python3 -S direct/power_pratt_fallback.py verify "$cert" --expected-base "${base%.json}"
done
python3 -S direct/check_square_power_nesting.py --shards direct/sealed --codec "$build/interval_witness_codec"
python3 -S direct/check_retained_coverage.py --square-codec "$build/square_codec" --power-codec "$build/interval_witness_codec"

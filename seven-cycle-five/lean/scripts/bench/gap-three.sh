#!/usr/bin/env bash
# Run from the Lean project root on Linux. The default is the stop-rule sample.
set -euo pipefail
sample_dir=$(mktemp -d)
trap 'rm -rf "$sample_dir"' EXIT
runtime=.lake/build/lib/libseven_x2dcycle_SevenCycleRuntime.so
lake build SevenCycleRuntime:shared SevenCycle.Bitsets.Orbit SevenCycle.AtlasData
lake env lean --root=scripts/bench -o "$sample_dir/G3Sig.olean" -c "$sample_dir/G3Sig.c" scripts/bench/G3Sig.lean
lake env leanc -DLEAN_EXPORTING -O3 -fPIC -shared "$sample_dir/G3Sig.c" "$runtime" -o "$sample_dir/G3Sig.so"
bench_path=$(lake env printenv LEAN_PATH)
LEAN_PATH="$sample_dir:$bench_path" lake env lean --plugin="$runtime" --plugin="$sample_dir/G3Sig.so" \
  --run scripts/bench/GapThree.lean "${1:-1016}" "${2:-32}"

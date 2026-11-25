#!/usr/bin/env bash
set -euo pipefail
if [[ ${1:-} != --timed-child ]]; then
    exec timeout --kill-after=15s 30m bash "$0" --timed-child "$@"
fi
shift
cd "${BT_WORKING_DIR:-$(dirname "$0")}"
# This bootstrap runs before measurement. A prebuilt image with these packages
# also works and avoids contacting package mirrors during job startup.
SECONDS=0
if ! command -v g++ >/dev/null || ! test -f /usr/include/gmpxx.h; then
    apt-get update -qq
    apt-get install -y --no-install-recommends g++ libgmp-dev gzip coreutils
fi
printf 'Dependency bootstrap seconds: %d\n' "$SECONDS"
python3 calibrate.py --cpus "${1:-8}" --rows "${PILOT_ROWS:-1000000}" --repeats "${PILOT_REPEATS:-3}"

if [[ ${PILOT_STORAGE_PROBE:-0} == 1 ]]; then
    results="${BT_CHECKPOINT_DIR:-.}/prime-pilot"
    python3 storage_probe.py "$results/sample.iw.gz" --mib 64 > "$results/storage.json.tmp"
    mv "$results/storage.json.tmp" "$results/storage.json"
    cat "$results/storage.json"
fi

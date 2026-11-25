#!/usr/bin/env bash
# Publish one range only after its saved witnesses decode and pass an independent verifier.
set -euo pipefail
if [[ $# -lt 3 || $# -gt 4 ]]; then
    echo "Usage: certify_power_shard.sh FIRST LAST OUTPUT_DIRECTORY [BINARY_DIRECTORY]" >&2
    exit 2
fi
first=$1
last=$2
if [[ ! $first =~ ^[1-9][0-9]*$ || ! $last =~ ^[1-9][0-9]*$ ]]; then
    echo 'Expected positive decimal endpoints' >&2
    exit 2
fi
out=$3
binaries=${4:-.}
mkdir -p -- "$out"
dest="$out/$first-$last.iw.gz"
if [[ -e "$dest" ]]; then
    echo "Existing shard: $dest" >&2
    exit 2
fi
scratch=$(mktemp "$out/.power-witness.XXXXXXXX")
trap 'rm -f -- "$scratch"' EXIT
generator=${INTERVAL_GENERATOR:-"$binaries/fast_power_witness"}
"$generator" "$first" "$last" --witnesses |
    "$binaries/interval_witness_codec" pack |
    gzip -1 -n > "$scratch"
gzip -dc -- "$scratch" |
    "$binaries/interval_witness_codec" unpack |
    "$binaries/check_power_witnesses" "$first" "$last"
# The temporary file and destination share a filesystem. Link fails if another
# worker already published the same range. It never replaces a certified shard.
ln -- "$scratch" "$dest"
if command -v sha256sum >/dev/null 2>&1; then
    sha256sum -- "$dest"
else
    shasum -a 256 "$dest"
fi

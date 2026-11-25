#!/usr/bin/env bash
# Replay Proposition 17 with a bounded number of ordinary Lake proof builds.
set -euo pipefail
cd "$(dirname "$0")/.."
jobs=${SEVEN_CYCLE_JOBS:-2}
if ! [[ "$jobs" =~ ^[1-9][0-9]*$ ]]; then
  echo "SEVEN_CYCLE_JOBS must be a positive integer" >&2
  exit 2
fi

lake build SevenCycle.TypeThree.Shards SevenCycle.Atlas.Complete33 SevenCycle.Atlas.PlanarKernel
for file in SevenCycle/Native/GapThree/P*S*.lean SevenCycle/Native/Census33/R*G*.lean; do
  module=${file%.lean}
  printf '%s\n' "${module//\//.}"
done | xargs -n 1 -P "$jobs" lake build
lake build SevenCycle.TypeThree.Result

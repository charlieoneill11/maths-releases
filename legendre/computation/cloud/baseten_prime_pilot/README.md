# Prime-witness calibration on Baseten

## Completed production run

The November 22–23, 2026 run completed the combined finite verification in **18 hours 53 minutes**. The fleet reached 230 CPU sandboxes after a staged ramp. All 319,488 production shards passed the coverage audit, with 59,162,481,759,320 production checks and 800,000,000 pilot checks (each pilot archive was fetched back and verified when it was made). All run sandboxes were released. [Coverage ledger](../../COVERAGE.md) · [Machine-readable results](combined-production-results.json)

| Workload | One-sandbox pilot, verified per second | Production, verified per active sandbox-second |
|---|---:|---:|
| Fast $11/5$ | 5.18 million | 6.66 million |
| Upper GMP | 1.21 million | 1.21 million |
| Squares | 4.48 million | 6.76 million |

Production averaged 870 million verified checks per second from launch to coverage confirmation (each check by the separate GMP verifier, inside the run). Estimated usage was 2,924 sandbox-hours, including the ramp and retries. The effective compute rate is unconfirmed. Two Hugging Face upload failures and one dependency bootstrap failure recovered using the existing receipts. The private bucket holds 51.69 TB (51,694,242,191,412 bytes in 639,242 files); this is its whole footprint, including the schedule and the receipts as well as the certificate archives. During the main fleet run, measured writes and readback each averaged roughly 1.0–1.4 GB/s across individual hours. The final completion time was set by the slowest square assignments.

Each shard receipt records the exact inclusive bounds, certificate checksums and the archive keys. The production worker fetched each archive, checked its SHA-256 and independently verified primality and strict interval membership before publishing the receipt. The final audit reconciled receipts and archive metadata against the frozen schedule. Prior retained evidence is replayed with the computation-level [replay.sh](../../replay.sh).

To audit the production schedule from the repository root, use an account with read access to the [private Hugging Face bucket](https://huggingface.co/buckets/baseten/prime-interval-certificates), the Hugging Face CLI and Python 3.12 or later.

```bash
bucket=baseten/prime-interval-certificates
digest=c7a9f9a2c86a11316936f92bba319ad0074437a0708165ae412c11b463758108
plan_dir="$(mktemp -d)"
hf buckets sync "hf://buckets/$bucket/plans/$digest/schedule/" "$plan_dir"
python3 legendre/computation/cloud/baseten_prime_pilot/production_worker.py \
  "$plan_dir" --bucket "$bucket" --expected-schedule "$digest" \
  --slots 1 --slot 0 --audit
```

What this command reads and establishes:

- It reads `plan.json` and `shards.jsonl` from the schedule folder and checks that the SHA-256 of `shards.jsonl` equals the digest above (and the digest recorded in `plan.json`). The digest authenticates `shards.jsonl` only. `plan.json`, which holds the per-kind totals and the digests of the seven pilot manifests, is not covered by it; compare it by hand with the `plan` object in [combined-production-results.json](combined-production-results.json).
- For every scheduled shard it reads the receipt from the bucket and checks that the receipt names the shard's kind, inclusive bounds, row count and exclusion file, that its pieces tile the shard without gaps, and that every certificate object it names exists with the recorded size. It checks the per-kind shard and row totals against `plan.json`.
- Slot 0 also fetches the seven pilot manifests named in `plan.json`, checks them against the digests there, and checks that their objects are distinct, that their row counts make up the difference between the baseline and the scheduled rows, and that the objects exist with the recorded sizes. It does not fetch or verify the pilot witnesses, so a pilot archive altered without changing its length would pass.
- It does not re-derive the coverage of the target ranges. `production_plan.py` checked, when the schedule was frozen, that the shards, the pilot ranges, the exclusions and the retained certificates tile the target ranges.

Add `--replay` (with a C++17 compiler, GMP, gzip and sufficient scratch space) to also fetch every production archive, check its SHA-256 against the receipt and rerun the GMP verifier on its witnesses. For parallel replay, assign slots 0 through 229 once each with `--slots 230`.

### Status of the evidence

The bucket is private, so none of the commands above can be run without read access to it. What can be checked without it is listed in the [computation README](../../README.md#what-the-public-files-establish): the retained certificates, replayed by [replay.sh](../../replay.sh), cover every $n\le3{,}883{,}865{,}444{,}451$ and, with Sorenson and Webster's verification, every $m\le70{,}500{,}002{,}100{,}000$, plus some isolated ranges. For the other bases below $3.5\times10^{13}$ and up to $10^{14}$ the finite results rest on the verification done inside the run, the receipts written after it, and the audit above.

A referee with read access replayed the 96 archives listed in three of the seven pilot manifests (160,000,000 rows: 64,000,000 square, 64,000,000 fast-power and 32,000,000 GMP bases; by these counts, the manifests of `runs/prime-pilot-hf-03`), and the archives matched the manifests. The other 640,000,000 pilot rows and all 59,162,481,759,320 production rows have not been replayed by anyone other than the run itself.

**Open: full pilot replay.** No program here replays the pilot in full. Such a replay needs read access to the bucket and would (1) check `plan.json` against the `plan` object in `combined-production-results.json`, and the seven pilot manifests against their digests there; (2) fetch every pilot archive and compare it with its SHA-256 in the manifest; (3) decode the witnesses according to their recorded kind and inclusive range and verify primality and the strict interval inequalities with `check_power_witnesses`; and (4) reconcile the pilot ranges, the production shards, the excluded square bases and the retained certificates against the target ranges, with no gap or double count. Replaying the production shards needs the same access and the audit command above with `--replay`.

## CPU sandbox pilot for the 35-trillion cutoff

The 230-sandbox allocation uses the Blaxel Sandboxes API in region `us-pdx-1`; set `BL_WORKSPACE` to your Blaxel workspace. Request 98,304 MiB per sandbox. The pilot observed 32 logical CPUs, 16 reported physical cores and AVX-512 IFMA. Run it from the repository root with Python 3.12 or later and `blaxel==0.4.23`. The launcher loads the indicated Hugging Face token file and uses the Blaxel CLI login when `BL_API_KEY` is unset.

```bash
env -u BL_API_KEY BL_WORKSPACE=<workspace> \
  python3 legendre/computation/cloud/baseten_prime_pilot/launch_sandbox.py \
  --name prime-pilot-hf-03 \
  --bucket baseten/prime-interval-certificates \
  --output /tmp/prime-pilot-hf-03 \
  --token-file "$HOME/.cache/huggingface/token"
```

This is the command for the completed pilot. For a new measurement, use a fresh name. The program generates two groups of disjoint shards per workload, uploads content-addressed archives to the private Hugging Face bucket, fetches them through the bucket API, checks SHA-256, and runs the independent GMP replay. The receipt is published after replay. The four-sandbox experiment used disjoint offsets, main-band certificates and a common upload start time. Its `total_seconds` includes the time waiting at the barrier. Use the transfer timestamps to measure aggregate storage throughput.

### Production schedules and resume

Run the computation-level `replay.sh` before using `production_plan.py` to freeze a schedule. Supply the built power and square codecs and the downloaded pilot receipts. The schedule uses inclusive bounds. It includes per-shard exclusion files for sparse square bases already certified by the retained power witnesses. The dense files keep the existing IW format. Sparse square files contain gzip-compressed decimal witness rows. The verifier checks every scheduled base and rejects missing, extra, or out-of-order witnesses.

Stage the plan files in `plans/<schedule-sha256>/schedule/` in the private bucket. The launcher accepts `--production-plan <schedule-sha256> --slot <index> --slots 230 --execute-approved` only for explicitly approved production allocations. Each slot owns a deterministic slice of the schedule. Use a new sandbox name for a retry and reuse the same schedule, slot and slot count after confirming the original process has ended. The worker reads existing receipts and checks the referenced archives still exist. It uploads and fetches fresh archives, replays every certificate, then writes receipts tied to the schedule. A search miss can fall back to the exact GMP search and a recursive Pratt proof. A shard remains open if no verifier accepts a witness.

### Staged production launch

Confirm the workspace’s effective hourly rate and at least 52 TB of writable private Hugging Face storage before allocating workers. Use `--start-kind main|square|gmp` to distribute the first workloads across the three kinds and `--max-waves` to stop a ramp worker at a receipt boundary. The worker logs new verified rows, upload and read-back bytes, wall time, and per-stage transfer timing after each wave. Exclude cached receipts from throughput. `--detach` prints the sandbox and process IDs for separate monitoring. A lost observer can reattach to the same process. Reconcile terminal state and delete the owned sandbox before reusing its slot.

Estimate completion from the remaining rows by kind, observed end-to-end rates, measured storage throughput, elapsed ramp time and final audit reserve. The initial 24-hour budget allows 21 productive hours, requiring about 683 MB/s of writes and a corresponding read-back. Grow to 230 only if the sustained run is on track for 24 hours. If a smaller fleet can meet the 32-hour fallback, finish or stop old slot owners before repartitioning with a new slot count. The immutable shard identities and receipts carry over across the repartition. Set the sandbox lifetime with `--wall-hours` to match the approved remaining window, up to 32 hours.

Auditing with `production_worker.py ... --audit` checks the frozen schedule, the pilot manifests and the production receipts as described under [Completed production run](#completed-production-run). Add `--replay` to fetch the production archives and repeat the arithmetic. For the pilot archives the audit checks manifest digests, row counts and object sizes only; it does not fetch and verify the pilot witnesses again. To distribute an audit, use the same slots as the run and require successful audit output from every slot. `--slots 1 --slot 0` audits the complete schedule from one process. Retained evidence predating the pilot is checked by `replay.sh`.

## Archived Training Job calibration

This single-node CPU Training Job **requests 8 vCPUs and 16 GiB of RAM**. It benchmarks the direct 11/5-power sweep and the consecutive-square component of the combined sweep. Truss 0.18.43 validates these resource fields locally. For this project, the completed pilot received backing instance `8x32` and started in 34 seconds with the default request. A separate 32-vCPU, 64-GiB request reported backing instance `64x128`, stayed queued for 30 minutes, and was stopped before starting. Check the Training Job quota and billing rate for the submitting workspace.

## What gets timed

For each workload the job measures 1, 4, and 8 simultaneous shard workers, rotating the order over three repetitions. Each worker generates two million witnesses per trial by default, split equally between opposite ends of the corresponding range. The square samples cover the ends near 70.5 and 100 trillion. The direct samples cover the ends near 3.88 and 32.65 trillion. All workers write real compressed archives to scratch, read them back, independently verify exact membership and primality, and hash the saved bytes. The report records compile and smoke-test time separately. The runner logs dependency bootstrap time. The program chooses AVX-512 IFMA when advertised and otherwise uses scalar arithmetic.

At the default settings this is 156 million calculated sample rows, including the repeated work, spread over both workloads. Peak retained trial data is roughly 15 MB at the observed archive sizes. One replayed sample and a JSON report are placed in `$BT_CHECKPOINT_DIR/prime-pilot`. Trial archives are discarded after each measurement. The checkpoint mechanism uploads asynchronously. Confirm the artifacts appear in the job's checkpoint list before treating them as durable.

`report.json` lists every trial, the CPU model, visible logical CPUs, affinity mask, OS-reported socket/core pairs in the mask, Linux cgroup quota, chosen backend and compiler version. Each `summary` entry gives `workers`, `direct_bases_per_second`, and `square_bases_per_second`. These are median completed bases per wall second across the allocation. Use the absolute rates at the desired worker count with the matching workload. The ratios to one worker describe scaling inside this allocation. CPU vendor, SMT, quota and contention can change those rates on another machine. For cluster forecasts repeat this pilot on multiple separate allocations and measure shared storage under concurrent load.

## Local check

On Linux install GNU C++ with C++17, the GMP development package, Python 3.8+, GNU coreutils, gzip and bash. From this directory, run a short test with the installed tools. This command uses local scratch and local output.

```bash
BT_CHECKPOINT_DIR="$(mktemp -d)" PILOT_REPEATS=1 PILOT_ROWS=8000 bash run.sh 2
```

On Debian the runner installs missing build dependencies before benchmarking. The supplied Baseten image uses Debian bookworm. It requires package mirror access and sufficient container privileges for that bootstrap. An alternative is a prebuilt image containing the listed packages. The GNU timeout in `run.sh` bounds bootstrap, compilation, benchmarks and the optional storage probe together to 30 minutes, with a 15-second termination grace period. Scheduling, image pull or build time, and platform teardown occur outside that limit.

## Validate and submit

Unzip the project into a fresh directory and run these commands from its project root. Install the Python SDK outside the upload directory. Validation uses the real SDK loader and can run before account login.

```bash
python3 -m venv /tmp/prime-truss-env
/tmp/prime-truss-env/bin/python -m pip install truss==0.18.43
/tmp/prime-truss-env/bin/python - <<'PY'
from pathlib import Path
from truss_train.loader import import_training_project
with import_training_project(Path("config.py")) as project:
    print(project.job.compute)
    print(project.job.runtime.start_commands)
PY
```

The expected compute fields are one node, 8 vCPUs, 16Gi, and no accelerator. The validated SDK version is 0.18.43. With an authorized CLI login, a confirmed workspace allocation and permission to incur the Training Job charge, the documented Baseten CLI command is

```bash
baseten train push --config config.py
```

The CLI shipped with the pinned Python package also provides `/tmp/prime-truss-env/bin/truss train push config.py` (positional config path). Choose one submission command. For an optional larger comparison, set both `PILOT_VCPUS=32` and `PILOT_MEMORY_GIB=64` in the submitter's environment. That request tests 1, 16, and 32 workers if it starts. The memory override takes a positive integer in GiB. Worker concurrency follows the CPU request independently. `PILOT_ROWS` and `PILOT_REPEATS` can also be set at submission. Their defaults are one million and three.

[CPU-only Training Jobs](https://docs.baseten.co/training/concepts/basics#cpu-only-jobs) · [Training SDK configuration](https://docs.baseten.co/reference/sdk/training) · [Job management](https://docs.baseten.co/training/management) · [Checkpoint sync](https://docs.baseten.co/training/concepts/checkpoints)

## Measure durable object-store bandwidth separately

The default job measures local scratch storage only. To test the production object store from the job, create a fresh, dedicated object key in the intended bucket and region. Generate a signed PUT URL and a signed GET URL for that same object with sufficient lifetime for queueing and execution. Bind their values through Baseten secrets named `prime_pilot_put_url` and `prime_pilot_get_url`. The PUT must accept a standard HTTPS request with Content-Length and no pre-specified Content-Type. The read must return the exact stored bytes. Supply URLs only through secrets. A successful run leaves a 64 MiB test object in storage.

Set `PILOT_STORAGE_PROBE=1` in the submitter's environment to add these references and enable the storage probe. The program builds a 64 MiB bandwidth fixture by repeating compressed bytes from a verified sample. It times the provider's PUT acknowledgement, fetches the same object from the store, and checks its full length and SHA-256. A matching retrieval produces `storage.json` containing the byte count, checksum, both elapsed times, and throughput in decimal MB/s. A failed retrieval or byte mismatch fails the job. Local scratch hashes and checkpoint staging throughput cannot establish this rate. One PUT measures the chosen object's path under the pilot's concurrency. Test concurrent uploads from multiple allocations before projecting a sustained fleet rate.

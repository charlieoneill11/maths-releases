"""Generate, store, fetch and independently replay a bounded certificate wave."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import file_digest
import json
import os
from pathlib import Path
import platform
import shlex
import subprocess
import tempfile
from time import perf_counter, sleep, time

from calibrate import cpu_description

HERE = Path(__file__).resolve().parent
DIRECT = HERE.parents[1] / "direct"
FAST_LAST = 32_700_000_000_000
BANDS = {
    "main": (6_000_000_000_000, 32_600_000_000_000),
    "square": (80_000_000_000_000, 99_900_000_000_000),
    "gmp": (32_710_000_000_000, 34_999_000_000_000),
}
GENERATE = 'set -o pipefail; "$1" "$2" "$3" --witnesses | "$4" pack | gzip -1 -n > "$5"'
REPLAY = 'set -o pipefail; gzip -dc "$1" | "$2" unpack | "$3" "$4" "$5"'


def compile_program(output, source, flags, gmp=False):
    subprocess.run(
        [*shlex.split(os.environ.get("CXX", "c++")), "-O3", "-std=c++17",
         *flags, str(DIRECT / source), *(["-lgmpxx", "-lgmp"] if gmp else []),
         "-o", str(output)], check=True,
    )


def compile_tools(directory, kind, backend):
    flags = ["-DPOWER_WITNESS_SQUARES"] if kind == "square" else []
    source = "verify_11_5" if kind == "gmp" else backend
    compile_program(directory / "generate", source + ".cpp", flags, gmp=True)
    compile_program(directory / "codec", "interval_witness_codec.cpp", flags)
    compile_program(directory / "verify", "check_power_witnesses.cpp",
                    [*flags, "-DUSE_GMP"], gmp=True)


def sha256(path):
    with path.open("rb") as stream:
        return file_digest(stream, "sha256").hexdigest()


def generate(binaries, first, last, path):
    tmp = path.with_suffix(".tmp")
    run = subprocess.run(
        ["bash", "-c", GENERATE, "generate", str(binaries / "generate"),
         str(first), str(last), str(binaries / "codec"), str(tmp)],
        capture_output=True, text=True,
    )
    if run.returncode:
        tmp.unlink(missing_ok=True)
        raise RuntimeError(f"Open range {first}..{last}: {run.stderr.strip()[-1200:]}")
    tmp.replace(path)


def replay(binaries, first, last, path):
    subprocess.run(
        ["bash", "-c", REPLAY, "replay", str(path), str(binaries / "codec"),
         str(binaries / "verify"), str(first), str(last)],
        stdout=subprocess.DEVNULL, check=True,
    )


def pilot_ranges(kind, workers, rows, offset):
    return [(start + offset + i * rows, start + offset + (i + 1) * rows - 1)
            for start in BANDS[kind] for i in range(workers // 2)]


def measure(kind, args, output, binaries):
    folder = output / kind
    folder.mkdir()
    rows = args.gmp_rows if kind == "gmp" else args.rows
    bounds = pilot_ranges(kind, args.workers, rows, args.offset)
    paths = [folder / f"{first}-{last}.iw.gz" for first, last in bounds]
    total = rows * len(paths)
    with ThreadPoolExecutor(args.workers) as pool:
        begin = perf_counter()
        list(pool.map(lambda item: generate(binaries, *item[0], item[1]), zip(bounds, paths)))
        generation_seconds = perf_counter() - begin
        byte_count = sum(path.stat().st_size for path in paths)
        digests = list(pool.map(sha256, paths))
        manifest = [{"kind": kind, "first": lo, "last": hi, "rows": hi - lo + 1,
                     "path": path.name, "sha256": digest, "bytes": path.stat().st_size}
                    for (lo, hi), path, digest in zip(bounds, paths, digests)]
        transfer = {}
        with tempfile.TemporaryDirectory(dir=output) as returned:
            inputs = paths
            if args.bucket:
                from huggingface_hub import batch_bucket_files, download_bucket_files

                # Content-addressed objects survive retries and are safe to share.
                keys = [f"certificates/{kind}/{item['first']}-{item['last']}/{item['sha256']}.iw.gz"
                        for item in manifest]
                for item, key in zip(manifest, keys):
                    item["object"] = key
                if args.upload_at:
                    sleep(max(0, args.upload_at - time()))
                transfer["put_started_at"] = time()
                started = perf_counter()
                batch_bucket_files(args.bucket, add=list(zip(paths, keys)))
                transfer["put_seconds"] = perf_counter() - started
                inputs = [Path(returned) / path.name for path in paths]
                transfer["put_finished_at"] = time()
                transfer["get_started_at"] = time()
                started = perf_counter()
                download_bucket_files(args.bucket, files=list(zip(keys, inputs)))
                transfer["get_seconds"] = perf_counter() - started
                transfer["get_finished_at"] = time()
            replay_start = perf_counter()
            if list(pool.map(sha256, inputs)) != digests:
                raise RuntimeError(f"{kind}: round-trip checksum mismatch")
            list(pool.map(lambda item: replay(binaries, *item[0], item[1]), zip(bounds, inputs)))
            replay_seconds = perf_counter() - replay_start
        receipt = json.dumps(manifest, sort_keys=True).encode() + b"\n"
        (folder / "manifest.json").write_bytes(receipt)
        if args.bucket:
            batch_bucket_files(args.bucket, add=[(receipt, f"runs/{args.run_id}/{kind}.json")])
        elapsed = perf_counter() - begin
    result = dict(kind=kind, intervals=total, bytes=byte_count, workers=args.workers,
                  generation_seconds=generation_seconds, replay_seconds=replay_seconds,
                  total_seconds=elapsed, verified_per_s=total / elapsed, **transfer)
    print(json.dumps(result), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--workers", type=int, default=32)
    parser.add_argument("--rows", type=int, default=2_000_000)
    parser.add_argument("--gmp-rows", type=int, default=1_000_000)
    parser.add_argument("--bucket")
    parser.add_argument("--run-id", default="smoke")
    parser.add_argument("--case", choices=BANDS, action="append")
    parser.add_argument("--offset", type=int, default=0)
    parser.add_argument("--upload-at", type=int, default=0)
    args = parser.parse_args()
    if args.workers < 2 or args.workers % 2 or min(args.rows, args.gmp_rows) < 1:
        parser.error("Use an even worker count and positive row counts")
    if max(args.rows, args.gmp_rows) * args.workers > 500_000_000:
        parser.error("Pilot bound exceeded")

    cpu = cpu_description()
    if args.bucket and (len(cpu["affinity"] or []) < args.workers or
                        (cpu["cgroup_v2_cpu_max"] or "").split()[0:1] == ["0"]):
        parser.error("The advertised sandbox cannot run the requested workers")
    backend = "fast_power_witness" if cpu["ifma_advertised"] else "portable_power_witness"
    info = {"cpu": cpu, "backend": backend, "platform": platform.platform(),
            "bucket": args.bucket, "run_id": args.run_id}
    print(json.dumps(info), flush=True)
    args.output = args.output.resolve()
    args.output.mkdir(parents=True)
    with tempfile.TemporaryDirectory() as build:
        results = []
        for kind in args.case or BANDS:
            directory = Path(build) / kind
            directory.mkdir()
            compile_tools(directory, kind, backend)
            results.append(measure(kind, args, args.output, directory))
        (args.output / "report.json").write_text(json.dumps(dict(info, workloads=results), indent=2) + "\n")


if __name__ == "__main__":
    main()

"""Benchmark generated, stored, and independently replayed 11/5-power witnesses."""
import argparse
import json
import os
import platform
import shutil
import statistics
import subprocess
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE / "src"


def read_optional(path):
    try:
        return Path(path).read_text().strip()
    except OSError:
        return None


def cpu_description():
    fields = {}
    for line in (read_optional("/proc/cpuinfo") or "").split("\n\n")[0].splitlines():
        key, _, value = line.partition(":")
        fields[key.strip()] = value.strip()
    flags = set(fields.get("flags", "").split())
    required = {"avx512f", "avx512dq", "avx512ifma"}
    affinity = sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else None
    core_pairs = set()
    for cpu in affinity or []:
        topology = f"/sys/devices/system/cpu/cpu{cpu}/topology"
        package = read_optional(topology + "/physical_package_id")
        core = read_optional(topology + "/core_id")
        if package is not None and core is not None:
            core_pairs.add((package, core))
    return {
        "architecture": platform.machine(),
        "model": fields.get("model name") or fields.get("Processor"),
        "visible_logical_cpus": os.cpu_count(),
        "affinity": affinity,
        "os_reported_socket_core_pairs_in_affinity": len(core_pairs) if core_pairs else None,
        "cgroup_v2_cpu_max": read_optional("/sys/fs/cgroup/cpu.max"),
        "ifma_advertised": required.issubset(flags),
    }


def compile_program(output, source, flags=()):
    subprocess.run(["g++", "-std=c++17", "-O3", str(SRC / source), *flags, "-o", str(output)],
                   check=True)


def trial(binaries, generator, directory, workers, rows, kind):
    run = subprocess.run(
        ["python3", str(SRC / "benchmark_interval_pipeline.py"), str(binaries),
         str(directory), "--kind", kind, "--workers", str(workers), "--rows", str(rows)],
        env=dict(os.environ, INTERVAL_GENERATOR=str(generator)), capture_output=True, text=True)
    if run.returncode:
        raise RuntimeError("Certificate pipeline failed.\n" + run.stderr[-1500:])
    report = json.loads(run.stdout[run.stdout.rindex("\n{"):])
    if report["rows"] != 2 * workers * rows:
        raise RuntimeError("Unexpected number of benchmark rows")
    return report


def calibration(args):
    scratch = Path(args.scratch).resolve()
    output = Path(args.output).resolve()
    scratch.mkdir(parents=True, exist_ok=True)
    output.mkdir(parents=True, exist_ok=True)
    cpu = cpu_description()
    use_ifma = args.backend == "ifma" or (args.backend == "auto" and cpu["ifma_advertised"])
    backend = "fast_power_witness" if use_ifma else "portable_power_witness"
    result = {
        "requested_vcpus": args.cpus,
        "requested_memory_gib": int(os.environ["PILOT_MEMORY_GIB"]) if "PILOT_MEMORY_GIB" in os.environ else None,
        "cpu": cpu, "backend": backend,
        "compiler": subprocess.check_output(["g++", "--version"], text=True).splitlines()[0],
        "rows_per_job": args.rows, "repeats": args.repeats, "trials": [],
    }
    print(json.dumps({k:v for k,v in result.items() if k != "trials"}), flush=True)
    with tempfile.TemporaryDirectory(prefix="prime-cal-", dir=scratch) as work:
        temporary = Path(work)
        kinds = ("direct", "square")
        compile_start = time.perf_counter()
        for kind in kinds:
            binaries = temporary / kind
            binaries.mkdir()
            flags = ["-DPOWER_WITNESS_SQUARES"] if kind == "square" else []
            compile_program(binaries / backend, backend + ".cpp", [*flags, "-lgmpxx", "-lgmp"])
            compile_program(binaries / "interval_witness_codec", "interval_witness_codec.cpp", flags)
            compile_program(binaries / "check_power_witnesses", "check_power_witnesses.cpp",
                            [*flags, "-DUSE_GMP", "-lgmpxx", "-lgmp"])
            sample = "70500002100001" if kind == "square" else "3883854444452"
            subprocess.run([str(binaries / backend), sample, sample, "--gmp-check"], check=True)
        result["compile_and_smoke_seconds"] = time.perf_counter() - compile_start
        concurrencies = sorted({1, max(1, args.cpus // 2), args.cpus})
        rates = {kind:{w:[] for w in concurrencies} for kind in kinds}
        for rep in range(args.repeats):
            # Rotate the order to reduce warm-up bias.
            offset = rep % len(concurrencies)
            for workers in concurrencies[offset:] + concurrencies[:offset]:
                for kind in (kinds if rep % 2 == 0 else reversed(kinds)):
                    with tempfile.TemporaryDirectory(prefix="shards-", dir=scratch) as out:
                        directory = Path(out)
                        binaries = temporary / kind
                        report = trial(binaries, binaries / backend, directory, workers, args.rows, kind)
                        report["replicate"] = rep + 1
                        result["trials"].append(report)
                        rates[kind][workers].append(report["whole_machine_bases_per_second"])
                        print(json.dumps(report), flush=True)
                        if rep == 0 and workers == args.cpus and kind == "direct":
                            shutil.copyfile(sorted(directory.glob("*.iw.gz"))[0],
                                            output / "sample.iw.gz")
        result["summary"] = []
        for count in concurrencies:
            row = {"workers":count}
            for kind in kinds:
                rate = statistics.median(rates[kind][count])
                row[kind+"_bases_per_second"] = rate
                row[kind+"_speedup_over_one_worker"] = rate / statistics.median(rates[kind][1])
            result["summary"].append(row)
    temp_report = output / "report.json.tmp"
    temp_report.write_text(json.dumps(result, indent=2)+"\n")
    temp_report.replace(output / "report.json")
    print(json.dumps({"summary":result["summary"]}, indent=2), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cpus", type=int, default=8)
    parser.add_argument("--rows", type=int, default=1_000_000)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--backend", choices=["auto", "portable", "ifma"], default="auto")
    parser.add_argument("--scratch", default=os.environ.get("BT_SCRATCH_DIR", tempfile.gettempdir()))
    parser.add_argument("--output", default=str(Path(os.environ.get("BT_CHECKPOINT_DIR", ".")) / "prime-pilot"))
    args = parser.parse_args()
    if not 1 <= args.cpus <= 256 or not 1 <= args.rows or not 1 <= args.repeats:
        parser.error("Expected positive rows and repeats, and 1 to 256 vCPUs")
    calibration(args)

"""Launch and observe one Blaxel pilot or one approved production slot."""
import argparse
import asyncio
from hashlib import sha256
from io import BytesIO
import json
import os
from pathlib import Path
import re
import shlex
import tarfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
IMAGE = "blaxel/base-image:latest"
REMOTE = "/tmp/prime-verification"
PROCESS = "prime-certificates"


def payload():
    compressed = BytesIO()
    with tarfile.open(fileobj=compressed, mode="w:gz") as bundle:
        for filename in ("calibrate.py", "sandbox_worker.py", "production_worker.py"):
            path = HERE / filename
            bundle.add(path, arcname=str(path.relative_to(ROOT)))
        for filename in ("fast_power_witness.cpp", "portable_power_witness.cpp",
                         "scalar_power_euler.hpp", "verify_11_5.cpp",
                         "interval_witness_codec.cpp", "check_power_witnesses.cpp", "power_pratt_fallback.py"):
            path = ROOT / "direct" / filename
            bundle.add(path, arcname=str(path.relative_to(ROOT)))
    return compressed.getvalue()


async def launch(args, token):
    from blaxel.core import SandboxInstance

    name = args.name
    production = args.production_plan is not None
    labels = {"owner": "charlieoneill", "run": name, "purpose": "prime-verification"}
    print(json.dumps({"sandbox": name, "workspace": os.environ["BL_WORKSPACE"],
                      "region": "us-pdx-1", "memory": 98_304}), flush=True)
    ttl_hours = args.wall_hours if production else None
    process_timeout = ttl_hours * 3600 - 100 if production else 1600
    async with asyncio.timeout(180):
        sandbox = await SandboxInstance.create({
            "name": name, "image": IMAGE, "region": "us-pdx-1",
            "memory": 98_304, "ttl": f"{ttl_hours}h" if production else "45m", "labels": labels,
            "snapshot_enabled": False,
        }, timeout=50)
    keep_on_exit = False
    try:
        async with asyncio.timeout(75):
            for attempt in range(12):
                try:
                    await asyncio.wait_for(sandbox.fs.ls("/tmp"), timeout=5)
                except Exception:
                    if attempt == 11:
                        raise
                    await asyncio.sleep(2)
                else:
                    break
            await sandbox.fs.write_binary("/tmp/prime-verification-src.tgz", payload())
        print(f"{name} is ready", flush=True)
        bucket_args = "" if args.scratch_only else f"--bucket {shlex.quote(args.bucket)}"
        install_hf = "" if args.scratch_only else "venv/bin/pip -q install huggingface_hub==2.4.0"
        case_args = " ".join("--case " + case for case in args.case)
        action = (
            f"venv/bin/python cloud/baseten_prime_pilot/sandbox_worker.py --run-id {shlex.quote(name)} "
            f"{bucket_args} --output output --workers 32 --rows {args.rows} "
            f"--gmp-rows {args.gmp_rows} {case_args} --offset {args.offset} --upload-at {args.upload_at}"
        )
        if production:
            install_hf = "venv/bin/pip -q install huggingface_hub==2.4.0 sympy==1.14.0"
            uri = shlex.quote(f"hf://buckets/{args.bucket}/plans/{args.production_plan}/schedule")
            start_kind = f"--start-kind {args.start_kind}" if args.start_kind else ""
            worker = (
                f"venv/bin/python cloud/baseten_prime_pilot/production_worker.py plan "
                f"--bucket {shlex.quote(args.bucket)} --expected-schedule {args.production_plan} "
                f"--slot {args.slot} --slots {args.slots}"
            )
            action = (
                f"venv/bin/hf buckets sync {uri} plan\n"
                f"{worker} --max-waves {args.max_waves} {start_kind} --execute"
            )
            if not args.max_waves:
                action += f"\n{worker} --audit"
        if install_hf:
            install_hf = f"{install_hf} || (sleep 3 && {install_hf}) || (sleep 8 && {install_hf})"
        command = f"""
set -euo pipefail
mkdir -p {REMOTE}
tar -xzf /tmp/prime-verification-src.tgz -C {REMOTE}
cd {REMOTE}
if ! printf '#include <gmpxx.h>\n' | c++ -x c++ -E - >/dev/null 2>&1 || ! python3 -m venv --help >/dev/null 2>&1; then
    privilege=()
    if [[ "$(id -u)" != "0" ]]; then privilege=(sudo -n); fi
    if command -v apt-get >/dev/null; then
        "${{privilege[@]}}" apt-get -o Acquire::Retries=2 update -qq
        "${{privilege[@]}}" apt-get -o Acquire::Retries=2 install -y -qq --no-install-recommends g++ libgmp-dev python3-venv gzip
    elif command -v apk >/dev/null; then
        "${{privilege[@]}}" apk add --no-cache g++ gmp-dev python3 py3-pip gzip
    else
        cat /etc/os-release >&2
        exit 127
    fi
fi
python3 -m venv venv
{install_hf}
{action}
"""
        try:
            async with asyncio.timeout(25):
                if production:
                    keep_on_exit = True
                await sandbox.process.exec({
                    "name": PROCESS, "command": "bash -c " + shlex.quote(command),
                    "env": {"HF_TOKEN": token or "", "HF_HUB_DISABLE_PROGRESS_BARS": "1",
                            "HF_HUB_DISABLE_TELEMETRY": "1"},
                    "keep_alive": True, "timeout": process_timeout,
                })
        except TimeoutError:
            print(f"Launch acknowledgement timed out. Observing {name}/{PROCESS}.", flush=True)
        if args.detach:
            state = await sandbox.process.get(PROCESS)
            print(json.dumps({"event": "production_dispatched", "sandbox": name,
                              "process": PROCESS, "slot": args.slot,
                              "status": state.status, "exit_code": state.exit_code}), flush=True)
            if state.status in {"failed", "killed", "completed", "stopped"}:
                keep_on_exit = False
                if state.status != "completed" or state.exit_code != 0:
                    raise RuntimeError(f"Production dispatch ended with {state.status}, exit {state.exit_code}")
            return
        state = await sandbox.process.wait(PROCESS,
                                           max_wait=(process_timeout + 100) * 1000,
                                           interval=30_000 if production else 3_000)
        keep_on_exit = False
        logs = await sandbox.process.logs(PROCESS, "all")
        (args.output / "sandbox.log").write_text(logs.replace(token, "[redacted]") if token else logs)
        if state.status != "completed" or type(state.exit_code) is not int or state.exit_code != 0:
            raise RuntimeError(f"{name}/{PROCESS}: {state.status}, exit {state.exit_code}")
        if production:
            print(f"{name}: slot {args.slot} {'sample' if args.max_waves else 'assignment'} finished", flush=True)
            return
        report = await sandbox.fs.read_binary(f"{REMOTE}/output/report.json")
        (args.output / "report.json").write_bytes(report)
        limit = asyncio.Semaphore(8)

        async def download(kind, item):
            async with limit:
                data = await sandbox.fs.read_binary(f"{REMOTE}/output/{kind}/{item['path']}")
                if sha256(data).hexdigest() != item["sha256"] or len(data) != item["bytes"]:
                    raise RuntimeError(f"Corrupt downloaded archive {kind}/{item['path']}")
                (args.output / kind / item["path"]).write_bytes(data)

        for kind in args.case or ("main", "square", "gmp"):
            manifest = await sandbox.fs.read_binary(f"{REMOTE}/output/{kind}/manifest.json")
            if args.scratch_only:
                (args.output / kind).mkdir(exist_ok=True)
                await asyncio.gather(*(download(kind, item) for item in json.loads(manifest)))
            (args.output / f"{kind}.json").write_bytes(manifest)
        print(report.decode(), flush=True)
    finally:
        if keep_on_exit:
            print(f"{name}/{PROCESS} may still be active. Observe or reconcile its terminal state before retrying slot {args.slot}.", flush=True)
        else:
            await delete_owned(sandbox, labels)


async def delete_owned(sandbox, labels):
    from blaxel.core import SandboxInstance

    name = labels["run"]
    if sandbox.metadata.labels.to_dict() != labels:
        raise RuntimeError(f"Verify ownership before deleting {name}")
    async with asyncio.timeout(45):
        await sandbox.delete()
        for _ in range(16):
            try:
                current = await SandboxInstance.get(name)
            except Exception as exc:
                if getattr(exc, "status_code", None) == 404:
                    print(f"Deletion verified for {name}", flush=True)
                    return
                raise
            if current.status == "TERMINATED":
                print(f"Termination verified for {name}", flush=True)
                return
            await asyncio.sleep(2)
    raise RuntimeError(f"Deletion not yet confirmed for {name}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--name", required=True)
    parser.add_argument("--bucket", default="baseten/prime-interval-certificates")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rows", type=int, default=2_000_000)
    parser.add_argument("--gmp-rows", type=int, default=1_000_000)
    parser.add_argument("--token-file", type=Path)
    parser.add_argument("--scratch-only", action="store_true")
    parser.add_argument("--case", choices=("main", "square", "gmp"), action="append", default=[])
    parser.add_argument("--offset", type=int, default=0)
    parser.add_argument("--upload-at", type=int, default=0)
    parser.add_argument("--production-plan", help="SHA-256 of the already staged production schedule")
    parser.add_argument("--slot", type=int, default=0)
    parser.add_argument("--start-kind", choices=("main", "square", "gmp"))
    parser.add_argument("--max-waves", type=int, default=0)
    parser.add_argument("--wall-hours", type=int, choices=range(1, 33), default=24)
    parser.add_argument("--slots", type=int, default=230)
    parser.add_argument("--execute-approved", action="store_true")
    parser.add_argument("--detach", action="store_true")
    args = parser.parse_args()
    if args.detach and not args.production_plan:
        parser.error("Only production launches can detach")
    if args.production_plan:
        if args.max_waves < 0:
            parser.error("The wave limit must be nonnegative")
        if not args.execute_approved or args.scratch_only:
            parser.error("A production slot requires explicit approval and a durable bucket")
        if not re.fullmatch(r"[0-9a-f]{64}", args.production_plan) or not 0 <= args.slot < args.slots <= 230:
            parser.error("Invalid schedule SHA-256 or slot allocation")
        if not re.fullmatch(r"prime-prod-[a-z0-9-]{4,42}", args.name):
            parser.error("Use a unique prime-prod-* name")
    elif not re.fullmatch(r"prime-pilot-[a-z0-9-]{4,42}", args.name):
        parser.error("Use a unique prime-pilot-* name")
    if not 1 <= min(args.rows, args.gmp_rows) <= max(args.rows, args.gmp_rows) <= 5_000_000:
        parser.error("Use 1 to 5,000,000 rows per shard")
    if not os.environ.get("BL_WORKSPACE"):
        parser.error("Set BL_WORKSPACE to your Blaxel workspace")
    token = args.token_file.read_text().strip() if args.token_file else os.environ.get("HF_TOKEN")
    if not token and not args.scratch_only:
        parser.error("Supply the HF token through --token-file or HF_TOKEN")
    args.output.mkdir(parents=True, exist_ok=True)
    try:
        asyncio.run(launch(args, token))
    except Exception as exc:
        parser.exit(1, (str(exc).replace(token, "[redacted]") if token else str(exc)) + "\n")


if __name__ == "__main__":
    main()

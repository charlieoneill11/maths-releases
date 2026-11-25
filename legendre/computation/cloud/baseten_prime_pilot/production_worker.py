"""Execute, resume, and audit an assigned slice of a frozen production schedule."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import gzip
from itertools import batched, islice
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import sys
from time import monotonic, sleep, time

from sandbox_worker import (
    DIRECT, GENERATE, compile_program, compile_tools, cpu_description, replay, sha256,
)

sys.path.insert(0, str(DIRECT))
import power_pratt_fallback

MISS = re.compile(r"(?:no witness in the guarded subinterval at n=|No certificate found for n=)(\d+)")
RECEIPT_FIELDS = ("kind", "first", "last", "rows", "exclusions", "exclusions_sha256")


def identity(entry):
    return {key: entry[key] for key in RECEIPT_FIELDS if key in entry}


def tag(entry):
    return f"{entry['kind']}/{entry['first']}-{entry['last']}"


def retry(operation, *args, **kwargs):
    for attempt in range(5):
        try:
            return operation(*args, **kwargs)
        except Exception as exc:
            response = getattr(exc, "response", None)
            code = getattr(response, "status_code", None)
            if attempt == 4 or (code is not None and code not in (408, 425, 429, 500, 502, 503, 504)):
                raise
            pause = response.headers.get("Retry-After", "") if response is not None else ""
            sleep(max(2 ** attempt, int(pause) if pause.isdigit() else 0))


def publish(api, bucket, additions):
    pending = additions
    for attempt in range(5):
        try:
            retry(api.batch_bucket_files, bucket, add=pending)
            return
        except Exception as exc:
            failures = getattr(exc, "failures", None)
            if (attempt == 4 or not failures or
                    any(item.get("error") != "File not found in Xet storage" for item in failures)):
                raise
            failed_paths = {item["path"] for item in failures}
            pending = [item for item in pending if item[1] in failed_paths]
            if len(pending) != len(failed_paths):
                raise
            sleep(2 ** attempt)


def ready_tools(directory, kind, backend):
    compile_tools(directory, kind, backend)
    compile_program(directory / "gmp", "verify_11_5.cpp", [], gmp=True)


def exclusions(entry, plan_dir, folder):
    path = plan_dir / entry["exclusions"]
    if sha256(path) != entry["exclusions_sha256"]:
        raise ValueError(f"Square exclusion checksum mismatch for {tag(entry)}")
    raw = folder / "exclusions.txt"
    rows = 0
    previous = entry["first"] - 1
    with gzip.open(path, "rt") as source, raw.open("w") as out:
        for line in source:
            base = int(line)
            if previous >= base or base > entry["last"]:
                raise ValueError(f"Invalid square exclusion at {base}")
            out.write(f"{base}\n")
            previous = base
            rows += 1
    if entry["last"] - entry["first"] + 1 - rows != entry["rows"]:
        raise ValueError(f"Square exclusion count mismatch for {tag(entry)}")
    return raw


def slice_exclusions(excluded, first, last, path):
    if excluded is None:
        return None
    with excluded.open() as source, path.open("w") as out:
        for line in source:
            base = int(line)
            if base > last:
                break
            if base >= first:
                out.write(line)
    return path


def gmp_square(binaries, first, last, raw, output):
    command = [str(binaries / "gmp"), str(first), str(last), "--legendre", "--witnesses"]
    if raw:
        command += ["--exclude", str(raw)]
    with output.open("wb") as stream:
        compressed = subprocess.Popen(["gzip", "-1", "-n"], stdin=subprocess.PIPE, stdout=stream)
        try:
            run = subprocess.run(command, stdout=compressed.stdin, stderr=subprocess.PIPE, text=True)
        finally:
            compressed.stdin.close()
            compressed_status = compressed.wait()
    return run.returncode or compressed_status, run.stderr


def generate_piece(binaries, kind, first, last, folder, excluded=None, fallback=False):
    archive = "tsv" if excluded or (kind == "square" and fallback) else "iw"
    path = folder / f"{first}-{last}.{archive}.gz"
    if archive == "tsv":
        code, stderr = gmp_square(binaries, first, last, excluded, path)
    else:
        engine = "gmp" if fallback else "generate"
        run = subprocess.run(
            ["bash", "-c", GENERATE, "generate", str(binaries / engine),
             str(first), str(last), str(binaries / "codec"), str(path)],
            capture_output=True, text=True,
        )
        code, stderr = run.returncode, run.stderr
    if code:
        path.unlink(missing_ok=True)
        failed = MISS.search(stderr)
        if not failed or not first <= int(failed[1]) <= last:
            raise RuntimeError(f"Open {kind} {first}..{last}: {stderr.strip()[-800:]}")
        base = int(failed[1])
        if first != last or (kind != "gmp" and not fallback):
            pieces = []
            if first < base:
                before = slice_exclusions(excluded, first, base - 1, folder / f"skip-{first}-{base-1}")
                pieces.extend(generate_piece(binaries, kind, first, base - 1, folder, before))
            pieces.extend(generate_piece(binaries, kind, base, base, folder, fallback=True))
            if base < last:
                after = slice_exclusions(excluded, base + 1, last, folder / f"skip-{base+1}-{last}")
                pieces.extend(generate_piece(binaries, kind, base + 1, last, folder, after))
            return pieces
        keep = power_pratt_fallback.generate(base, 4096, 20000, 128, square=kind == "square")
        if keep is None:
            raise RuntimeError(f"Open {kind} {base}: GMP and Pratt search exhausted")
        archive = "pratt"
        path = folder / f"{base}-{base}.pratt.gz"
        path.write_bytes(gzip.compress(json.dumps(keep, sort_keys=True).encode(), mtime=0))
    checksum = sha256(path)
    key = f"certificates/{kind}/{first}-{last}/{checksum}.{archive}.gz"
    return [dict(first=first, last=last, object=key, sha256=checksum, bytes=path.stat().st_size,
                 archive=archive, name=path.name)]


def verify_piece(binaries, kind, item, path, excluded):
    if path.stat().st_size != item["bytes"] or sha256(path) != item["sha256"]:
        raise ValueError(f"Bad durable checksum for {item['object']}")
    first, last = item["first"], item["last"]
    excluded = slice_exclusions(excluded, first, last, path.with_suffix(".exclusions"))
    if item["archive"] == "pratt":
        if excluded and excluded.stat().st_size:
            raise ValueError(f"Unexpected Pratt certificate for excluded base {first}")
        with gzip.open(path, "rt") as stream:
            power_pratt_fallback.verify(first, json.load(stream), square=kind == "square")
    elif item["archive"] == "iw":
        replay(binaries, first, last, path)
    else:
        command = ['set -o pipefail; gzip -dc "$1" | "$2" "$3" "$4" "${@:5}"',
                   "replay", str(path), str(binaries / "verify"), str(first), str(last)]
        if excluded:
            command.append(str(excluded))
        subprocess.run(["bash", "-c", *command], stdout=subprocess.DEVNULL, check=True)


def check_receipt(entry, receipt):
    if identity(entry) != receipt["shard"]:
        raise ValueError(f"Receipt disagrees with the plan for {tag(entry)}")
    cursor = entry["first"]
    pieces = receipt["pieces"]
    for item in pieces:
        first, last = item["first"], item["last"]
        checksum, archive = item["sha256"], item["archive"]
        expected = f"certificates/{entry['kind']}/{first}-{last}/{checksum}.{archive}.gz"
        if (first != cursor or last < first or not re.fullmatch(r"[0-9a-f]{64}", checksum)
                or archive not in ("iw", "tsv", "pratt") or item["object"] != expected
                or (archive == "pratt" and first != last)
                or item["bytes"] <= 0 or item["name"] != f"{first}-{last}.{archive}.gz"
                or (archive == "tsv" and entry["kind"] != "square")
                or (entry.get("exclusions") and archive == "iw")):
            raise ValueError(f"Invalid piece for {tag(entry)}")
        cursor = last + 1
    if cursor != entry["last"] + 1:
        raise ValueError(f"Receipt leaves a gap for {tag(entry)}")


def run_wave(api, args, entries, prefix, tools, root, pool):
    started_at, started = time(), monotonic()
    folder = Path(tempfile.mkdtemp(dir=root))
    receipts = {f"{prefix}/receipts/{tag(entry)}.json": entry for entry in entries}
    cached = {item.path for item in retry(lambda: list(api.get_bucket_paths_info(args.bucket, receipts)))}
    records = []
    pending = []
    local = {}

    for key, entry in receipts.items():
        subdir = folder / tag(entry)
        subdir.mkdir(parents=True)
        raw = exclusions(entry, args.plan_dir, subdir) if entry.get("exclusions") else None
        local[key] = (entry, key, subdir, raw)
    if cached:
        retry(api.download_bucket_files, args.bucket,
              [(key, local[key][2] / "receipt.json") for key in cached],
              raise_on_missing_files=True)
    for key, item in local.items():
        entry, _, subdir, _ = item
        if key in cached:
            receipt = json.loads((subdir / "receipt.json").read_text())
            check_receipt(entry, receipt)
            records.append((*item, receipt))
        else:
            pending.append(item)
    all_objects = {piece["object"]: piece["bytes"]
                   for _, _, _, _, receipt in records for piece in receipt["pieces"]}
    missing = set()
    for group in batched(all_objects, 64):
        reported = {f.path: f.size for f in retry(
            lambda: list(api.get_bucket_paths_info(args.bucket, group)))}
        missing.update(key for key in group if reported.get(key) != all_objects[key])
    if missing:
        available = []
        for record in records:
            if any(piece["object"] in missing for piece in record[4]["pieces"]):
                pending.append(record[:4])
            else:
                available.append(record)
        records = available

    def generate_entry(item):
        entry, key, subdir, raw = item
        pieces = generate_piece(tools[entry["kind"]], entry["kind"], entry["first"],
                                entry["last"], subdir, raw)
        receipt = dict(shard=identity(entry), pieces=pieces)
        check_receipt(entry, receipt)
        return entry, key, subdir, raw, receipt

    if args.audit and pending:
        raise RuntimeError(f"Missing receipt for {tag(pending[0][0])}")
    # Retry another allocation only for the entries whose receipt is still absent.
    generation_start = monotonic()
    fresh = []
    for item, future in zip(pending, [pool.submit(generate_entry, item) for item in pending]):
        try:
            fresh.append(future.result())
        except (RuntimeError, ImportError) as exc:
            print(str(exc), flush=True)

    generation_seconds = monotonic() - generation_start
    put_seconds = get_seconds = 0.0
    put_started_at = get_started_at = None
    uploaded_bytes = fetched_bytes = 0
    if fresh:
        uploads = [(subdir / piece["name"], piece["object"])
                   for _, _, subdir, _, receipt in fresh for piece in receipt["pieces"]]
        uploaded_bytes = sum(piece["bytes"] for *_, receipt in fresh for piece in receipt["pieces"])
        put_started_at, put_start = time(), monotonic()
        publish(api, args.bucket, uploads)
        put_seconds = monotonic() - put_start
    if fresh or args.replay:
        verify = records + fresh if args.replay else fresh
        downloads = []
        checks = {}
        for entry, key, subdir, raw, receipt in verify:
            work = checks[key] = []
            for piece in receipt["pieces"]:
                path = subdir / ("returned-" + piece["name"])
                downloads.append((piece["object"], path))
                fetched_bytes += piece["bytes"]
                work.append((tools[entry["kind"]], entry["kind"], piece, path, raw))
        get_started_at, get_start = time(), monotonic()
        retry(api.download_bucket_files, args.bucket, downloads, raise_on_missing_files=True)
        get_seconds = monotonic() - get_start

        def verify_entry(work):
            for check in work:
                verify_piece(*check)

        futures = {key: pool.submit(verify_entry, work) for key, work in checks.items()}
        failed = set()
        for key, future in futures.items():
            try:
                future.result()
            except (OSError, ValueError, subprocess.CalledProcessError) as exc:
                if args.audit:
                    raise
                failed.add(key)
                print(f"Open after replay failure {key}: {exc}", flush=True)
        fresh = [item for item in fresh if item[1] not in failed]
        records = [item for item in records if item[1] not in failed]
    if fresh:
        publish(api, args.bucket,
                [(json.dumps(receipt, sort_keys=True).encode() + b"\n", key)
                 for _, key, _, _, receipt in fresh])
    shutil.rmtree(folder)
    print(json.dumps(dict(event="production_wave", slot=getattr(args, "slot", None),
                          audit=args.audit, kind=entries[0]["kind"], started_at=started_at,
                          finished_at=time(), seconds=monotonic() - started,
                          new_verified_rows=sum(entry["rows"] for entry, *_ in fresh),
                          uploaded_bytes=uploaded_bytes, fetched_bytes=fetched_bytes,
                          generation_seconds=generation_seconds, put_started_at=put_started_at,
                          put_seconds=put_seconds, get_started_at=get_started_at, get_seconds=get_seconds, open_shards=len(entries)-len(records)-len(fresh))),
          flush=True)
    return len(records) + len(fresh), sum(entry["rows"] for entry, *_ in records + fresh)


def audit_pilots(api, args, plan, folder):
    expected = {kind: plan["baseline"][kind] - count for kind, count in plan["rows"].items()}
    found = {kind: 0 for kind in expected}
    objects = {}
    paths = [(key, folder / str(index)) for index, key in enumerate(plan["pilot_receipts"])]
    if paths:
        retry(api.download_bucket_files, args.bucket, paths, raise_on_missing_files=True)
    for key, path in paths:
        if sha256(path) != plan["pilot_receipts"][key]:
            raise ValueError(f"Pilot receipt checksum mismatch: {key}")
        for item in json.loads(path.read_text()):
            kind = item["kind"]
            if kind in found:
                found[kind] += item["rows"]
                if item["object"] in objects:
                    raise ValueError("Duplicate pilot object")
                objects[item["object"]] = item["bytes"]
    if found != expected:
        raise ValueError("Pilot rows disagree with the frozen plan")
    for group in batched(objects, 64):
        reported = {f.path: f.size for f in retry(
            lambda: list(api.get_bucket_paths_info(args.bucket, group)))}
        if reported != {key: objects[key] for key in group}:
            raise ValueError("Pilot certificate object is missing or has changed in size")


def run(args):
    from huggingface_hub import HfApi

    plan = json.loads((args.plan_dir / "plan.json").read_text())
    schedule = args.plan_dir / "shards.jsonl"
    checksum = sha256(schedule)
    if checksum != plan["schedule_sha256"] or (
            args.expected_schedule and checksum != args.expected_schedule):
        raise ValueError("Production schedule checksum mismatch")
    prefix = f"plans/{checksum}"
    api = HfApi()
    cpu = cpu_description()
    backend = "fast_power_witness" if cpu["ifma_advertised"] else "portable_power_witness"
    with tempfile.TemporaryDirectory(dir=args.scratch) as work:
        root = Path(work)
        if args.audit and args.slot == 0:
            audit_pilots(api, args, plan, root)
        tools = {}
        for kind in plan["rows"]:
            tools[kind] = root / kind
            tools[kind].mkdir()
            if not args.audit or args.replay:
                ready_tools(tools[kind], kind, backend)
        by_kind = {kind: [] for kind in plan["rows"]}
        with schedule.open() as stream:
            for index, line in enumerate(stream):
                if index % args.slots == args.slot:
                    entry = json.loads(line)
                    by_kind[entry["kind"]].append(entry)
        if args.start_kind and args.start_kind not in by_kind:
            raise ValueError(f"Workload {args.start_kind} absent from schedule")
        kinds = list(by_kind)
        if args.start_kind:
            kinds.remove(args.start_kind)
            kinds.insert(0, args.start_kind)
        batches = (batch for kind in kinds for batch in batched(by_kind[kind], args.workers))
        if args.max_waves:
            batches = islice(batches, args.max_waves)
        with ThreadPoolExecutor(args.workers) as pool:
            total = done = planned_rows = done_rows = 0
            for batch in batches:
                count, rows = run_wave(api, args, batch, prefix, tools, root, pool)
                done += count
                total += len(batch)
                planned_rows += sum(entry["rows"] for entry in batch)
                done_rows += rows
                print(json.dumps(dict(plan=checksum, slot=args.slot, complete_shards=done,
                                      assigned_shards=total, verified_rows=done_rows,
                                      assigned_rows=planned_rows)), flush=True)
    if args.slots == 1 and not args.max_waves and (total != sum(plan["shards"].values()) or
                            planned_rows != sum(plan["rows"].values())):
        raise RuntimeError("Schedule totals disagree with the frozen plan")
    if done != total or done_rows != planned_rows:
        raise SystemExit(f"Slot {args.slot} still has {total - done} open shards")
    print(json.dumps(dict(event="production_slot_completed", plan=checksum, slot=args.slot,
                          slots=args.slots, partial=bool(args.max_waves), audited=args.audit,
                          shards=done, rows=done_rows)), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("plan_dir", type=Path)
    parser.add_argument("--bucket", required=True)
    parser.add_argument("--expected-schedule")
    parser.add_argument("--workers", type=int, default=32)
    parser.add_argument("--slots", type=int, default=230)
    parser.add_argument("--slot", type=int, required=True)
    parser.add_argument("--start-kind", choices=("main", "square", "gmp"))
    parser.add_argument("--max-waves", type=int, default=0)
    parser.add_argument("--scratch", type=Path)
    parser.add_argument("--audit", action="store_true")
    parser.add_argument("--replay", action="store_true")
    parser.add_argument("--execute", action="store_true",
                        help="Allow generating shards and writing production receipts")
    args = parser.parse_args()
    if not 0 <= args.slot < args.slots or not 1 <= args.workers <= 32:
        parser.error("Invalid slot or worker count")
    if args.max_waves < 0 or (args.audit and args.max_waves):
        parser.error("A wave limit is available only for execution")
    if not args.audit and not args.execute:
        parser.error("Production generation requires --execute")
    run(args)

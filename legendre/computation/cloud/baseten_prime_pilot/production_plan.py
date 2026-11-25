"""Freeze exact inclusive 35T sweep bounds and the replayed square exclusions."""
import argparse
from collections import Counter
import csv
import gzip
from hashlib import file_digest
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "direct"))
from check_retained_coverage import (
    FIRST, HERE, PILOT_STARTS, PREFIX, TARGET, complement, root_floor,
    square_credits, square_to_power,
)
from sandbox_worker import FAST_LAST

BRIDGE_LAST = 35_000_000_000_000 - 1
SPARSE_LAST = 70_500_239_607_437
BASELINE = {
    "combined": {"main": 27_363_298_754_255, "gmp": 2_299_998_999_999,
                 "square": 29_499_984_005_066},
    "power": {"main": 28_816_132_443_267, "gmp": 2_299_998_999_999},
}


def split(first, last, width):
    for lo in range(first, last + 1, width):
        yield lo, min(lo + width - 1, last)


def digest(path):
    with path.open("rb") as stream:
        return file_digest(stream, "sha256").hexdigest()


def retained_power():
    archives = []
    for folder in ("sealed", "continuation"):
        for path in (HERE / folder).glob("*.iw.gz"):
            lo, hi = map(int, path.name.split(".")[0].split("-"))
            archives.append((lo, hi, path))
    return sorted(archives)


def load_pilots(paths, mode):
    pilot = {"main": [], "gmp": [], "square": []}
    for path in paths:
        for item in json.loads(path.read_text()):
            kind = item["kind"]
            if kind == "square" and mode == "power":
                continue
            lo, hi = item["first"], item["last"]
            if item["rows"] != hi - lo + 1 or len(item["sha256"]) != 64 or not item.get("object"):
                raise ValueError(f"Invalid durable pilot receipt {path}")
            pilot[kind].append((lo, hi))
    for bounds in pilot.values():
        bounds.sort()
        if any(left[1] >= right[0] for left, right in zip(bounds, bounds[1:])):
            raise ValueError("Pilot receipts overlap")
    return pilot


def square_ranges(args, archives, credit):
    # All archived power witnesses yielding sparse credits lie in this initial segment.
    # The two retained square pilots and new pilot shards lie above the sparse credits.
    sparse_bounds = list(split(PREFIX + 1, SPARSE_LAST, args.sparse_rows))
    with (HERE / "alternative-square-credits.tsv").open() as stream:
        alternates = sorted(int(row["m"]) for row in csv.DictReader(stream, delimiter="\t"))
    current = 0
    path = args.output / "exclusions"
    path.mkdir()
    count = Counter()
    files = {}

    def write(base):
        nonlocal current
        if not PREFIX < base <= SPARSE_LAST:
            raise ValueError(f"Sparse square credit outside frozen bounds: {base}")
        index = (base - PREFIX - 1) // args.sparse_rows
        if index != current:
            if current in files:
                files.pop(current).close()
            current = index
        if index not in files:
            lo, hi = sparse_bounds[index]
            files[index] = (path / f"{lo}-{hi}.txt").open("w")
        files[index].write(f"{base}\n")
        count[index] += 1

    excluded = iter(alternates)
    extra = next(excluded, None)

    def on_credit(base):
        nonlocal extra
        while extra is not None and extra < base:
            write(extra)
            extra = next(excluded, None)
        write(base)

    try:
        canonical, alternatives = square_credits(args.power_codec, archives, on_credit)
        while extra is not None:
            write(extra)
            extra = next(excluded, None)
    finally:
        for stream in files.values():
            stream.close()
    if sum(count.values()) != canonical + alternatives:
        raise ValueError("Sparse exclusion count mismatch")
    if any(lo <= SPARSE_LAST for lo, _ in credit):
        raise ValueError("Pilot intersects sparse block")
    for index, (lo, hi) in enumerate(sparse_bounds):
        rows = hi - lo + 1 - count[index]
        if rows:
            entry = dict(kind="square", first=lo, last=hi, rows=rows)
            if count[index]:
                relative = f"exclusions/{lo}-{hi}.txt"
                raw = args.output / relative
                with raw.open("rb") as source, (args.output / (relative + ".gz")).open("wb") as target:
                    with gzip.GzipFile(fileobj=target, mode="wb", filename="", mtime=0) as archive:
                        while block := source.read(1024 * 1024):
                            archive.write(block)
                raw.unlink()
                entry.update(exclusions=relative + ".gz",
                             exclusions_sha256=digest(args.output / (relative + ".gz")))
            yield entry
    existing = [(lo, lo + 999_999) for _, lo in PILOT_STARTS]
    for lo, hi in complement(SPARSE_LAST + 1, TARGET, existing + credit):
        for first, last in split(lo, hi, args.rows):
            yield dict(kind="square", first=first, last=last, rows=last - first + 1)


def plan(args):
    archives = retained_power()
    retained = [(lo, hi) for lo, hi, _ in archives]
    retained.extend(square_to_power(args.square_codec))
    for path in (HERE / "examples").glob("pratt-fallback-*.json"):
        n = int(path.stem.rsplit("-", 1)[1])
        retained.append((n, n))
    lower = root_floor(TARGET**10, 11) + 1 if args.mode == "combined" else FIRST
    pilot = load_pilots(args.pilot_manifest, args.mode)
    expected = BASELINE[args.mode].copy()
    for kind in expected:
        expected[kind] -= sum(hi - lo + 1 for lo, hi in pilot[kind])
    args.output.mkdir(parents=True)
    tasks = Counter()
    rows = Counter()
    schedule = args.output / "shards.jsonl"
    with schedule.open("w") as stream:
        def emit(entry):
            tasks[entry["kind"]] += 1
            rows[entry["kind"]] += entry["rows"]
            stream.write(json.dumps(entry, sort_keys=True, separators=(",", ":")) + "\n")

        bands = {"main": (lower, FAST_LAST, args.rows),
                 "gmp": (FAST_LAST + 1, BRIDGE_LAST, args.gmp_rows)}
        for kind, (first, last, width) in bands.items():
            for lo, hi in complement(first, last, retained + pilot[kind]):
                for a, b in split(lo, hi, width):
                    emit(dict(kind=kind, first=a, last=b, rows=b - a + 1))
        if args.mode == "combined":
            for entry in square_ranges(args, archives, pilot["square"]):
                emit(entry)
    if rows != expected:
        raise ValueError(f"Plan did not reconcile to the verified ledger: {rows} vs {expected}")
    summary = dict(mode=args.mode, baseline=BASELINE[args.mode], rows=rows, shards=tasks,
                   pilot_receipts={f"runs/{path.parent.name}/{path.name}": digest(path)
                                   for path in args.pilot_manifest},
                   schedule_sha256=digest(schedule))
    (args.output / "plan.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=BASELINE)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--square-codec", type=Path, required=True)
    parser.add_argument("--power-codec", type=Path, required=True)
    parser.add_argument("--pilot-manifest", type=Path, action="append", default=[])
    parser.add_argument("--rows", type=int, default=250_000_000)
    parser.add_argument("--gmp-rows", type=int, default=25_000_000)
    parser.add_argument("--sparse-rows", type=int, default=8_000_000)
    args = parser.parse_args()
    if min(args.rows, args.gmp_rows, args.sparse_rows) <= 0:
        parser.error("Shard widths must be positive")
    plan(args)

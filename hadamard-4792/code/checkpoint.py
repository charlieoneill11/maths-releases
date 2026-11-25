"""Save or restore complete per-band search records with their input fingerprints."""
import argparse
import json
from pathlib import Path

from campaign import fingerprint


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("save", "restore"))
    parser.add_argument("survivors", type=Path)
    parser.add_argument("work", type=Path)
    parser.add_argument("checkpoint", type=Path)
    args = parser.parse_args()
    bands = json.loads(args.survivors.read_text())
    if args.mode == "save":
        rows = [json.loads(path.read_text()) for path in args.work.glob("g*-case*.json")
                if not path.name.endswith("-witness.json")]
    else:
        rows = [json.loads(line) for line in args.checkpoint.read_text().splitlines()]
    rows.sort(key=lambda row: (row["generator"], row["index"]))
    seen = set()
    for row in rows:
        gen, index = row["generator"], row["index"]
        band = bands[index]
        key = (gen, index)
        if (key in seen or gen not in (4, 5) or not 0 <= index < len(bands)
                or row["spec"] != band["spec"] or row["tau"] != band["tau"]
                or row["band_sha256"] != fingerprint(band, gen)):
            raise ValueError(f"inconsistent record for {key}")
        if row["hit"]:
            raise ValueError(f"preserve and independently check the witness for {key}")
        seen.add(key)
    if args.mode == "save":
        args.checkpoint.write_text("".join(json.dumps(row, sort_keys=True, separators=(",", ":"))
                                           + "\n" for row in rows))
    else:
        args.work.mkdir(parents=True, exist_ok=True)
        for row in rows:
            path = args.work / f'g{row["generator"]}-case{row["index"]}.json'
            if path.exists():
                if json.loads(path.read_text())["band_sha256"] != row["band_sha256"]:
                    raise ValueError(f"conflicting record at {path}")
            else:
                path.write_text(json.dumps(row, sort_keys=True) + "\n")
    print(f"{len(rows)} completed cases")


if __name__ == "__main__":
    main()

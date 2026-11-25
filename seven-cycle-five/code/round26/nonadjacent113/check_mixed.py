"""Check the mixed census by ordered transverse marking, after source normalization."""
import argparse
import csv
from collections import Counter, defaultdict
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent


def check_mixed(layouts, products):
    expected = {}
    with (HERE / "mixed-profiles.tsv").open() as stream:
        for row in csv.DictReader(stream, delimiter="\t"):
            pattern = row["transverse_gaps"]
            assert pattern not in expected
            assert row["ordered_case"] == "".join(sorted("2" + pattern))
            expected[pattern] = int(row["source_pairs"]), int(row["layouts"])
    assert set(expected) == {"".join(g) for g in product("23", repeat=3)} - {"222"}
    counts = Counter()
    sources = defaultdict(set)
    seen = set()
    with Path(layouts).open() as stream:
        for row in stream:
            first, second, motion, overlap, x, y, z = map(int, row.split())
            assert 0 <= first < 1016 and 0 <= second < 1016 and 0 <= motion < 16464
            assert 0 <= overlap <= 33 and all(0 <= t < 14 for t in (x, y, z))
            key = first, second, motion, x, y, z
            assert key not in seen
            seen.add(key)
            pattern = "".join(str(2 + t // 7) for t in (x, y, z))
            assert pattern in expected
            counts[pattern] += 1
            sources[pattern].add((first, second, motion))
    for pattern, pair in expected.items():
        assert pair == (len(sources[pattern]), counts[pattern])
    assert Path(products).read_bytes() == b""
    print(f"Verified seven ordered transverse gap patterns, {len(seen):,} layouts and zero products.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("layouts", type=Path)
    parser.add_argument("products", type=Path)
    args = parser.parse_args()
    check_mixed(args.layouts, args.products)

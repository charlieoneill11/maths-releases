"""Replay the distance-two source, choosing the registered transverse gaps."""
import argparse
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ATLAS = HERE.parents[1] / "round25/multiplicities/atlas/atlas.tsv"
SOURCE_PAIRS = 16_939_304_704


def run(mode, folder, target):
    binaries = {}
    for name in ("candidate_pairs", "match_middle", "join_projections", "audit_projections"):
        binary = folder / name
        subprocess.run(["c++", "-O3", "-std=c++17", str(HERE / (name + ".cpp")),
                        "-o", binary], check=True)
        binaries[name] = binary
    pairs = folder / "source-pairs.bin"
    layouts = folder / "layouts.tsv"
    products = folder / "products.tsv"
    def output(name, *args):
        result = subprocess.run([binaries[name], ATLAS, *args], check=True,
                                text=True, stdout=subprocess.PIPE)
        return result.stdout.splitlines()

    summary = output("candidate_pairs", mode, pairs)[-1].split()
    assert summary[0:5:2] == ["tested", "compatible", "hist"]
    examined, retained = int(summary[1]), int(summary[3])
    histogram = list(map(int, summary[5:]))
    assert examined == SOURCE_PAIRS and len(histogram) == 34
    assert sum(histogram) == retained == pairs.stat().st_size // 8
    assert pairs.stat().st_size == 8*retained

    rows = [list(map(int, line.split())) for line in output("match_middle", pairs, mode, layouts, str(target))]
    assert len(rows) == 34 and all(len(row) == 6 for row in rows)
    assert [r[0] for r in rows] == list(range(34)) and [r[1] for r in rows] == histogram
    records = [tuple(map(int, line.split())) for line in layouts.read_text().splitlines()]
    assert len(records) == len(set(records)) == sum(row[5] for row in rows)
    for first, second, motion, common, *starts in records:
        assert 0 <= first < 1016 and 0 <= second < 1016 and 0 <= motion < 16464
        assert 0 <= common <= 33 and len(starts) == 3 and all(0 <= s < 14 for s in starts)
        assert (mode == "mixed") == any(s >= 7 for s in starts)

    join = output("join_projections", layouts, products)
    result = re.fullmatch(r"layouts (\d+) compatible prefixes (\d+) surviving layouts (\d+) "
                          r"eight-projection products (\d+)", join[-1])
    assert result
    total, prefixes, live_layouts, live_products = map(int, result.groups())
    assert total == len(records)
    print(f"Target {target}, {mode}: {examined:,} projection pairs, {retained:,} pairs after planar filtering")
    print(f"{sum(r[2] for r in rows):,} placements tested, {total:,} after the matching test")
    print(f"{prefixes:,} projection prefixes, {live_layouts:,} layouts and "
          f"{live_products:,} complete products after joining six transverse bands")
    assert live_layouts == live_products == 0 and products.stat().st_size == 0
    if target == 113 and mode == "mixed":
        from check_mixed import check_mixed
        check_mixed(layouts, products)
    audit = output("audit_projections", layouts)
    check = re.fullmatch(r"Independent direct-coordinate audit: (\d+) layouts, "
                         r"(\d+) planar-compatible, (\d+) height-compatible", audit[-1])
    assert check and int(check[1]) == total and int(check[3]) == 0
    expected_planar = 125 if mode == "2222" else int(target == 113)
    assert int(check[2]) == expected_planar
    print(audit[-1])
    return retained, sum(r[2] for r in rows), sum(r[4] for r in rows), total


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("2222", "mixed"), default="2222")
    parser.add_argument("--target", type=int, choices=(112, 113), default=113,
                        help="use two middle levels of size 15 for target 112")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as tmp:
        counts = run(args.mode, Path(tmp), args.target)
    if args.target == 112:
        expected = ((9_767_343, 25_578_139, 611, 615) if args.mode == "2222"
                    else (16_076_232, 96_313_808, 8_720, 9_975))
        assert counts == expected
    elif args.mode == "2222":
        assert counts == (9_767_343, 25_578_139, 889, 894)
    else:
        assert counts == (16_076_232, 96_313_808, 15_051, 17_702)

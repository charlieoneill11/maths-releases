"""Uniform per-incidence locked-star saving on the cap16 partial wave."""

import json
import subprocess
from bisect import bisect_right
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory

from joint6_mask_cost import verify_pi

ROOT = Path(__file__).resolve().parent
S = 10**12
MICRO = 10**6


def wall_floor(profile, y):
    i = bisect_right(profile, [y, S]) - 1
    a, u = profile[i]
    if y == a:
        return u
    b, v = profile[i + 1]
    return ((b - y) * u + (y - a) * v) // (b - a)


def boxes(spec):
    # All coordinates are in millionths. Higher rows follow the same facing wall.
    for y in range(1, 250000 - 10, 10):
        right = wall_floor(spec["right"], y * MICRO) // MICRO
        for a, b in ((1, 4), (4, 10), (10, 20), (20, 40), (40, 70)):
            yield 6, (right - b, right - a, y, y + 10)
    for y in range(9170, 18000, 20):
        left = wall_floor(spec["left"], y * MICRO) // MICRO + 1
        for a, b in ((0, 2), (2, 5), (5, 12), (12, 25), (25, 45), (45, 80), (80, 135), (135, 200)):
            yield 4, (left + a, left + b, y, y + 20)
    for x in [*range(4300, 11000, 25), *range(861000, 874750, 25)]:
        for a, b in ((1, 4), (4, 10), (10, 20), (20, 40), (40, 75)):
            yield 2, (x, x + 25, a, b)
    # Native-label counts, independent of Fourier estimates on the preceding boxes.
    for y in range(5, 9160, 20):
        left = wall_floor(spec["left"], y * MICRO) // MICRO + 1
        for a, b in (
            (0, 5),
            (5, 15),
            (15, 30),
            (30, 55),
            (55, 90),
            (90, 150),
            (150, 240),
            (240, 360),
            (360, 540),
        ):
            yield 0, (left + a, left + b, y, y + 20)


def run():
    verify_pi()
    spec_file = ROOT / "cap16_finite_wave.json"
    digest = sha256(spec_file.read_bytes()).hexdigest()
    old = json.loads((ROOT / "cap17_finite_clip_result.json").read_text())["geometry"]
    assert digest == old["profile_sha256"]
    spec = json.loads(spec_file.read_text())
    assert 9 * S // 10 < spec["x"] < S
    for wall in ("left", "right"):
        rows = spec[wall]
        assert rows == sorted(rows) and len(rows) == len(dict(rows))
        assert rows[0][0] == 0 and rows[-1][0] == S // 2 and rows[len(rows) // 2][0] == S // 4
        assert all(
            a[1] == b[1] and a[0] + b[0] == S // 2 and 0 <= a[1] < S
            for a, b in zip(rows, reversed(rows))
        )
        sign = 1 if wall == "right" else -1
        assert all(sign * (b[1] - a[1]) >= 0 for a, b in zip(rows[: len(rows) // 2], rows[1:]))
    work = list(boxes(spec))
    # Sweep the y edges to verify that all four source families have disjoint interiors.
    # At each event a box ending is removed before any new box begins.
    events = []
    for _, b in work:
        x, X, y, Y = b
        events.extend(((y, 1, x, X), (Y, 0, x, X)))
    active = set()
    by_height = {}
    for y, r, x, X in events:
        by_height.setdefault(y, []).append((r, x, X))
    for y in sorted(by_height):
        for r, x, X in sorted(by_height[y]):
            if r:
                assert (x, X) not in active
                active.add((x, X))
            else:
                active.remove((x, X))
        intervals = sorted(active)
        assert all(b <= c for (a, b), (c, d) in zip(intervals, intervals[1:]))
    assert not active
    words = [str(2 * spec["x"])]
    for name in ("left", "right"):
        rows = spec[name]
        words.append(str(len(rows)))
        words.extend(str(i) for pair in rows for i in pair)
    lines = [" ".join(words)]
    lines.extend(" ".join(map(str, (c, *(v * MICRO for v in b)))) for c, b in work)
    with TemporaryDirectory() as tmp:
        binary = Path(tmp) / "moments"
        subprocess.run(
            ["g++", "-O3", "-std=c++17", str(ROOT / "cap22_partial_star.cpp"), "-o", str(binary)],
            check=True,
        )
        result = subprocess.run(
            [str(binary)], input="\n".join(lines), capture_output=True, text=True, check=True
        ).stdout
    bound, *proof = result.splitlines()
    tag, target, low_count, high_count = bound.split()
    assert tag == "bound"
    final, large_degree = proof.pop().split()
    assert final == "native"
    orders = {}
    for row in proof:
        kind, d, k = row.split()
        assert kind == "degree"
        orders[d] = int(k)
    return dict(
        profile_sha256=digest,
        per_incidence_excess_picounits=int(target),
        right_and_alternate_boxes=int(low_count),
        native_only_boxes=int(high_count),
        native_alone_from_degree=int(large_degree),
        first_passing_fejer_order_changes=orders,
        quarter_circle_bins=131072,
        max_harmonic=512,
        threshold_denominator=10000,
    )


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))

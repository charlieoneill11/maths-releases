"""Exact cap17 forest credits for the collision-free second-layer radius."""

import json
from fractions import Fraction as F
from hashlib import sha256

from cap15_finite_nested import PI_HI, ROOT, credits, down
from refit_wave_check import Hole


def geometry():
    wave = ROOT / "cap16_finite_wave.json"
    previous = json.loads((ROOT / "cap17_finite_clip_result.json").read_text())["geometry"]
    assert sha256(wave.read_bytes()).hexdigest() == previous["profile_sha256"]
    spec = json.loads(wave.read_text())
    hole = Hole(spec)
    a, d, w = F(53, 20000), F(1837, 500000), F(73, 10000)
    # A cone pair has horizontal difference <= 2w. Two blank tails must
    # then belong to the same column. Their vertical difference <= w²/2.
    width = F(2 * max(hole.w), 10**12)
    assert 2 * w + width < F(2 * spec["x"], 10**12)
    assert width**2 + w**4 / 4 < (2 * d) ** 2

    count = 16384
    g = credits(a, d, count, spec)
    previous_h = F(1)
    unit = []
    for i in range(1, count + 1):
        t = w * i / count
        previous_h = min(previous_h, hole.overlap(t, t * t / 2))
        unit.append(previous_h)
    assert g["B"] == previous["B"] == down(2 * w * sum(unit) / (count * PI_HI))

    for name, field, radius, fraction in (
        ("first", "C", a, F(3, 4)),
        ("second", "E", d, F(3, 10)),
    ):
        values = []
        for i in range(8192):
            u, v = F(i, 8192), F(i + 1, 8192)
            h = hole.overlap(2 * radius * (1 - u * u) / (1 + u * u), 4 * radius * v / (1 + v * v))
            values.append((h, 2 * (v - u) / (1 + v * v)))
        assert g[field] == down(2 * sum(h * weight for h, weight in values) / PI_HI)
        cap = fraction * max(h for h, _ in values)
        g[field] = down(2 * sum(min(h, cap) * weight for h, weight in values) / PI_HI)
        g[name + "_cap_fraction"] = str(fraction)
        g[name + "_max_short"] = str(cap)
        g[name + "_retained_per_mille"] = 1000 * sum(max(0, h - cap) for h in unit) // sum(unit)
    g["disjoint_D_tail_events"] = True
    g["K"] = 0
    for key in ("blank", "edge_probability", "angle_bins", "profile_sha256"):
        g[key] = previous[key]
    return g


if __name__ == "__main__":
    print(json.dumps(geometry(), indent=2))

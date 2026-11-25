"""Verify this order-4792 difference family by enumerating ordered differences."""
import argparse
import json
from itertools import product
from pathlib import Path


MODULI = (7, 19, 3, 3)
MASKS = (
    (0x0C85B, 0x1C32A, 0x03CDC),
    (0x08573, 0x07C3C, 0x187C2),
    (0x08328, 0x09E3D, 0x16D4B),
    (0x04AD2, 0x03E65, 0x1991B),
)


def expand_masks(points):
    orbit_id = {}
    next_label = 0
    for x, y in product(range(7), range(19)):
        if (x, y) in orbit_id:
            continue
        while (x, y) not in orbit_id:
            orbit_id[x, y] = next_label
            x, y = 2 * x % 7, 4 * y % 19
        next_label += 1
    if next_label != 17:
        raise ValueError("incorrect number of multiplier orbits")
    sequences = []
    for masks in MASKS:
        signs = []
        for x, y, u, v in points:
            field_class = int(u != 0) + int(v != 0)
            minus = (masks[field_class] >> orbit_id[x, y]) & 1
            signs.append("-" if minus else "+")
        sequences.append("".join(signs))
    return sequences


def check(certificate, check_masks):
    if (certificate["order"] != 4792 or certificate["construction"] != "spence"
            or tuple(certificate["group"]) != MODULI):
        raise ValueError("unexpected order, construction or group")
    points = list(product(*(range(m) for m in MODULI)))
    signs = certificate["sequences"]
    if len(signs) != 4 or any(len(s) != len(points) or set(s) - {"+", "-"} for s in signs):
        raise ValueError("expected four length-1197 sign strings")
    counts = [0] * len(points)
    sizes = []
    for sequence in signs:
        negative = [g for g, sign in zip(points, sequence) if sign == "-"]
        sizes.append(len(negative))
        for x, y, u, v in negative:
            for a, b, c, d in negative:
                shift = (((x-a) % 7 * 19 + (y-b) % 19) * 3 + (u-c) % 3) * 3 + (v-d) % 3
                counts[shift] += 1
    if any(abs(len(points) - 2 * size) != 1 for size in sizes) or counts[0] != sum(sizes):
        raise ValueError(f"unexpected negative-set sizes {sizes} or zero count {counts[0]}")
    multiplicity = sum(sizes) - len(points) - 1
    for g, count in zip(points[1:], counts[1:]):
        if count != multiplicity:
            raise ValueError(f"shift {g} has {count} ordered differences, expected {multiplicity}")
    print("Negative-set sizes:", *sizes)
    print(f"Ordered differences: {counts[0]} at zero, {multiplicity} at each of the 1196 nonzero shifts")
    print("Summed periodic autocorrelation: 4788 at zero, -4 everywhere else")
    if check_masks:
        if expand_masks(points) != signs:
            raise ValueError("the orbit masks and expanded certificate differ")
        print("All 4788 signs agree with the twelve orbit masks")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--check-masks", action="store_true")
    args = parser.parse_args()
    check(json.loads(args.certificate.read_text()), args.check_masks)

"""Exact fixed-margin lift filters for one pair of projected solutions."""
import argparse
from collections import Counter
import json
from math import prod
from pathlib import Path

import numpy as np

from joint import fibre_keys, sheet_fibres


def lifts(data):
    labels, fibres = sheet_fibres(data["generator"])
    weights = np.bincount(labels.ravel())
    ids = np.arange(1 << len(weights), dtype=np.int32)
    mass = np.zeros(len(ids), dtype=np.int16)
    for i, w in enumerate(weights):
        mass += w*((ids >> i) & 1).astype(np.int16)
    blocks = []
    for a, b in zip(data["rows7"], data["rows19"]):
        sheets = [np.array(fibres[k], dtype=np.int32) for k in fibre_keys(a, b)]
        triples = np.stack(np.meshgrid(*sheets, indexing="ij"), axis=-1).reshape(-1, 3)
        x, y, z = triples.T
        same = (len(ids)-1) ^ (y ^ z)
        cost = 6*mass[same]+4*mass[same & ~(x ^ y)]
        blocks.append((triples, cost))
    return labels, blocks


def distribution(cost):
    weights, counts = np.unique(cost, return_counts=True)
    return {int(w): int(c) for w, c in zip(weights, counts)}


def cost_join(blocks):
    ways = {0: 1}
    for triples, cost in blocks:
        updated = Counter()
        histogram = distribution(cost)
        for a, n in ways.items():
            for b, m in histogram.items():
                if a+b <= 528:
                    updated[a+b] += n*m
        ways = updated
    return ways.get(528, 0)


def field_array(orbit_signs, labels):
    # In F_3[i], i^2 = -1, the four squares in F_9^* lie on the two axes.
    plane = np.array([[0 if x == y == 0 else 1 if x*y == 0 else 2
                       for y in range(3)] for x in range(3)])
    return orbit_signs[labels[:, :, None, None], plane]


def paf_check(arrays, expected):
    axes = tuple(range(arrays.ndim-1))
    shape = arrays.shape[1:]
    for shift in np.ndindex(shape):
        actual = sum(int((x*np.roll(x, shift, axes)).sum()) for x in arrays)
        if actual != expected(shift):
            raise ValueError(f"shift {shift}, expected {expected(shift)}, got {actual}")


def check_margins(data, labels):
    expanded = []
    for masks in data["sheet_masks"]:
        signs = 2*((np.array(masks) >> np.arange(labels.max()+1)[:, None]) & 1)-1
        expanded.append(field_array(signs, labels))
    arrays = np.array(expanded)
    if arrays.shape != (4,7,19,3,3) or np.any(arrays.sum(axis=(1,2,3,4)) != 1):
        raise ValueError("wrong full dimensions or block sums")
    for p, other, axis, reps in ((7,19,2,(0,1,3)), (19,7,1,(0,1,2))):
        projected = arrays.sum(axis=axis)
        literal = projected[:,reps]
        rows = np.stack((literal[:,:,0,0], literal[:,:,0,1], literal[:,:,1,1]), axis=-1)
        if rows.tolist() != data[f"rows{p}"]:
            raise ValueError("orbit masks disagree with the stored margins")
        paf_check(projected, lambda s: (4792 if not any(s) else 0) - 4*other)
    return arrays


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("node", type=Path)
    args = parser.parse_args()
    data = json.loads(args.node.read_text())
    labels, blocks = lifts(data)
    check_margins(data, labels)
    sizes = [len(rows) for rows, _ in blocks]
    if sizes != data["block_lifts"]:
        raise ValueError("unexpected fibre sizes")
    print("both projected PAFs verified at every shift")
    print("block lifts", sizes, "total", prod(sizes))
    print("minimum costs", [int(c.min()) for _, c in blocks])
    print("quadruples satisfying the defect identity", cost_join(blocks))

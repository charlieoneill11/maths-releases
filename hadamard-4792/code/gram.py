"""Rebuild an odd Spence matrix and verify every pair by XOR and population count."""
import argparse
import hashlib
import json
import math
from pathlib import Path

import numpy as np


def check(certificate, expected_order):
    mods = tuple(certificate["group"])
    v = math.prod(mods)
    order = 4 * (1 + v)
    sequences = certificate["sequences"]
    if (certificate["construction"] != "spence" or v % 2 != 1
            or order != expected_order or order != certificate["order"]
            or len(sequences) != 4 or any(len(s) != v or set(s) - {"+", "-"} for s in sequences)):
        raise ValueError("wrong construction, order or sign data")
    signs = [np.frombuffer(s.encode(), dtype=np.uint8) == ord("-") for s in sequences]
    # Each table entry names a signed input block. For a negative label flip the sign.
    labels = ((1, 2, 3, 4), (-2, 1, 4, -3), (-3, -4, 1, 2), (-4, 3, -2, 1))
    row_sums = [v - 2 * int(x.sum()) for x in signs]
    if any(abs(s) != 1 for s in row_sums):
        raise ValueError("invalid odd Spence border")
    border = np.array([[(row_sums[abs(i)-1] < 0) != (i < 0) for i in row] for row in labels])
    positions = np.array(list(np.ndindex(mods)))
    rows = []
    digest = hashlib.sha256()

    def consume(bits):
        # One bit per column, including the border. int conversion discards only leading zeros.
        rows.append(int.from_bytes(np.packbits(bits).tobytes(), "big"))
        digest.update(b",".join(np.where(bits, b"-1", b"1")) + b"\n")

    for b in range(4):
        consume(np.concatenate((~border[b], np.repeat(border[b], v))))
    for b, label_row in enumerate(labels):
        for g in positions:
            parts = [border[b]]
            for j, label in enumerate(label_row):
                if b == j:
                    arguments = positions - g
                elif b == 0 or j == 0:
                    arguments = -positions - g
                else:
                    arguments = positions + g
                indices = np.ravel_multi_index((arguments % mods).T, mods)
                parts.append(signs[abs(label)-1][indices] ^ (label < 0))
            consume(np.concatenate(parts))
    for i, x in enumerate(rows):
        for j in range(i):
            if (x ^ rows[j]).bit_count() * 2 != order:
                raise ValueError(f"nonorthogonal rows {j}, {i}")
    actual = digest.hexdigest()
    if certificate.get("sha256", actual) != actual:
        raise ValueError(f"canonical CSV digest mismatch: {actual}")
    print(f"order {order}, {len(rows)} sign rows, {order*(order-1)//2} off-diagonal pairs, sha256 {actual}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    parser.add_argument("order", type=int)
    args = parser.parse_args()
    check(json.loads(args.certificate.read_text()), args.order)

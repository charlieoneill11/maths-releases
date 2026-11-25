"""Draw the figure of the order-4792 Hadamard matrix from the published CSV file.

Usage: python3 make_figure.py H4792.csv.gz OUTDIR      (needs NumPy and Pillow)

Writes OUTDIR/H4792.png (one pixel per entry, +1 white and -1 black) and
OUTDIR/H4792-corner.png (the top-left 200 x 200 entries, each drawn as a
5 x 5 block of pixels).
"""
import gzip
import sys
from pathlib import Path

import numpy as np
from PIL import Image


def main(csv_path, outdir):
    raw = gzip.open(csv_path).read() if csv_path.endswith(".gz") else open(csv_path, "rb").read()
    H = np.array([[e == b"1" for e in line.split(b",")] for line in raw.split(b"\n")[:-1]])
    if H.shape != (4792, 4792):
        raise SystemExit(f"unexpected shape {H.shape}")
    out = Path(outdir)
    Image.fromarray(H).save(out / "H4792.png", optimize=True)
    corner = np.kron(H[:200, :200], np.ones((5, 5), dtype=bool))
    Image.fromarray(corner).save(out / "H4792-corner.png", optimize=True)
    print("wrote", out / "H4792.png", "and", out / "H4792-corner.png")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    main(sys.argv[1], sys.argv[2])

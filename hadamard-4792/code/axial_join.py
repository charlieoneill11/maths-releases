"""Check the transitive-prime quotient with a collision-free packed integer join."""
import argparse
from pathlib import Path


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("spectra",type=Path)
    args=parser.parse_args()
    rows=[tuple(map(int,line.split())) for line in args.spectra.read_text().splitlines()]
    if not rows:
        print("empty single-block pool")
        return
    # Each of the four entries is in [0,4792], so base 32768 has no carries.
    def pack(values):
        return sum(x << (15*i) for i,x in enumerate(values))
    target=pack([4792]*len(rows[0]))
    keys=[pack(row) for row in rows]
    pairs={a+b for i,a in enumerate(keys) for b in keys[:i+1]}
    live=sum(target-v in pairs for v in pairs)
    print(f"{len(rows)} block spectra, {len(pairs)} pair sums, {live} complementary pair sums")


if __name__=="__main__":
    main()

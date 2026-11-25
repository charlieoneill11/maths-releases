"""Audit an orbit-sheet candidate by literal translations on each quotient and on G.

Python 3 standard library only. A nonzero status from --require-full means the
candidate does not give the required Spence certificate.
"""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path


def group(mods):
    return list(product(*(range(m) for m in mods)))


def develop(data):
    sheets = data["sheets"]
    generator = data["generator"]
    moduli = (7,19,3,3)
    orbit_count = 0
    index = {}
    for i,j in group((7,19)):
        if (i,j) in index:
            continue
        orbit = []
        x,y = i,j
        while (x,y) not in orbit:
            orbit.append((x,y))
            x,y = (2*x)%7, (generator*y)%19
        for point in orbit:
            index[point] = orbit_count
        orbit_count += 1
    if orbit_count != 17 or len(sheets)!=4 or any(len(b)!=17 for b in sheets):
        raise ValueError("wrong orbit data")
    arrays = []
    for block in sheets:
        if any(len(r)!=3 or set(r)-{-1,1} for r in block):
            raise ValueError("invalid sheet sign")
        f = {}
        for i,j,x,y in group(moduli):
            field_class = 0 if (x,y)==(0,0) else 2 if x and y else 1
            f[i,j,x,y] = block[index[i,j]][field_class]
        arrays.append(f)
    return arrays


def project(arrays, axes):
    result = [Counter() for _ in arrays]
    for row, out in zip(arrays,result):
        for point, value in row.items():
            out[tuple(point[i] for i in axes)] += value
    return result


def correlations(blocks, mods):
    points = group(mods)
    pos = {p:i for i,p in enumerate(points)}
    rows = [[b[p] for p in points] for b in blocks]
    for shift in points:
        perm = [pos[tuple((a+b)%m for a,b,m in zip(h,shift,mods))] for h in points]
        yield shift,sum(sum(x*y[j] for x,j in zip(y,perm)) for y in rows)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("data",type=Path)
    parser.add_argument("--require-full",action="store_true")
    args = parser.parse_args()
    a = develop(json.loads(args.data.read_text()))
    mods = (7,19,3,3)
    for axes, kernel in (((0,1),9),((0,2,3),19),((1,2,3),7),((0,1,2,3),1)):
        b = project(a,axes)
        bad = Counter()
        for shift,value in correlations(b,tuple(mods[j] for j in axes)):
            residual = value - ((4792 if not any(shift) else 0)-4*kernel)
            if residual:
                bad[residual]+=1
        print(f"kernel {kernel}, incorrect shifts {sum(bad.values())}, residuals {dict(sorted(bad.items()))}")
        if bad and (kernel!=1 or args.require_full):
            raise SystemExit(1)


if __name__ == "__main__":
    main()

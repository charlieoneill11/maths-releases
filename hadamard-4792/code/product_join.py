"""Meet complementary product-multiplier blocks and emit a full Spence witness on a hit."""
import argparse
from collections import defaultdict
import json
from pathlib import Path

import numpy as np

from native_join import Join


def full_signs(masks, field):
    result = []
    for row in masks:
        sequence = []
        for i, j, a, b in np.ndindex(7,19,3,3):
            x = 0 if i == 0 else 1 if i in (1,2,4) else 2
            y = 0 if j == 0 else 1 if j in (1,4,5,6,7,9,11,16,17) else 2
            if field == 3:
                t = 0 if a == b == 0 else 1 if (a == 0 or b == 0) else 2
            else:
                t = int(a != 0) + 2*int(b != 0)
            sequence.append("-" if (row[t] >> (3*x + y)) & 1 else "+")
        result.append("".join(sequence))
    return result


def meet_spectra(masks, raw, dc, target, library):
    powers, ix = np.unique(raw, axis=0, return_index=True)
    masks = masks[ix]
    groups = defaultdict(list)
    for i, row in enumerate(dc[ix]):
        groups[tuple(map(int,row))].append(i)
    keys = list(groups)
    buckets = [np.array(groups[key],dtype=np.int32) for key in keys]
    pairs = defaultdict(list)
    for j, b in enumerate(keys):
        for i, a in enumerate(keys[:j+1]):
            sums = tuple(x+y for x,y in zip(a,b))
            if max(sums) <= 4792:
                pairs[sums].append((i,j))
    plans = set()
    for sums, pairs1 in pairs.items():
        for i,j in pairs1:
            for k,l in pairs.get(tuple(4792-x for x in sums),()):
                plans.add(tuple(sorted((i,j,k,l))))
    coeff = np.random.default_rng(479299).bit_generator.random_raw(len(target))
    h = powers.astype(np.uint64) @ coeff
    want = target.astype(np.uint64) @ coeff
    join = Join(library)
    total = overlaps = 0
    for plan in sorted(plans):
        blocks = [buckets[i] for i in plan]
        a,b,c,d = sorted(map(len,blocks))
        total += a*d + b*c
        for found in join([(h[block],block) for block in blocks],want):
            overlaps += 1
            if np.array_equal(powers[found].sum(axis=0),target):
                return masks[found]
    print(f"{len(raw)} rows, {len(powers)} distinct spectra, {len(plans)} field-DC tuples, "
          f"{total} pair entries, {overlaps} fingerprint matches, zero solutions")
    return None


def save_signs(signs, output):
    from lift import paf_check
    arrays=np.array([[1 if c=="+" else -1 for c in s] for s in signs],dtype=np.int16).reshape(4,7,19,3,3)
    paf_check(arrays,lambda h:(4792 if not any(h) else 0)-4)
    cert=dict(order=4792,construction="spence",group=[7,19,3,3],sequences=signs)
    output.write_text(json.dumps(cert)+"\n")
    print(f"full witness written to {output}")


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("field",choices=("qr","klein"))
    parser.add_argument("rows",type=Path)
    parser.add_argument("library",type=Path)
    parser.add_argument("output",type=Path)
    args=parser.parse_args()
    f=3 if args.field=="qr" else 4
    rows=np.loadtxt(args.rows,dtype=np.int32,ndmin=2)
    if rows.shape[1]!=6*f:
        raise ValueError("incorrect row format")
    powers=rows[:,f:]
    target=np.tile([4792,4792,4792,16*4792,0],f)
    target[0]=4
    hit=meet_spectra(rows[:,:f],powers,powers[:,5::5],target,args.library)
    if hit is not None:
        save_signs(full_signs(hit,f),args.output)


if __name__=="__main__":
    main()

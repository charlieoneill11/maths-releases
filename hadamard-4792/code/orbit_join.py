"""Find a complete odd Spence quadruple in an arbitrary scalar K-orbit shape."""
import argparse
from pathlib import Path
from collections import defaultdict

import numpy as np

from product_join import save_signs
from native_join import Join
from orbit_profile import dc_plans,dc_rows,open_rows


def solve(shape, name, path, library, output):
    with shape.open() as src:
        _, lags = map(int,src.readline().split())
        labels = np.array(list(map(int,src.readline().split()))).reshape(7,19)
    rows,field,lags=open_rows(shape,name,path)
    runs=defaultdict(list)
    counts=dc_rows(rows,field,runs)
    keys,plans=dc_plans(counts)
    if not plans:
        print("zero solutions")
        return
    required=np.zeros((field,lags),dtype=np.int32)
    required[:,0]=4792
    required[0,:]-=36
    coeff=np.random.default_rng(479203).bit_generator.random_raw(field*lags)
    want=required.ravel().astype(np.uint64) @ coeff
    hashes=np.empty(len(rows),dtype=np.uint64)
    columns={}
    used={i for job in plans for i in job}
    for i in used:
        key=keys[i]
        parts=[]
        for start,end in runs[key]:
            parts.append(np.arange(start,end,dtype=np.int32))
            for k in range(start,end,32768):
                stop=min(end,k+32768)
                hashes[k:stop]=rows[k:stop,2*field:].astype(np.uint64) @ coeff
        ids=np.concatenate(parts)
        columns[i]=(hashes[ids],ids)
    join=Join(library)
    matches=0
    masks=None
    for job in sorted(plans):
        for found in join([columns[i] for i in job],want):
            matches+=1
            if np.array_equal(rows[found,2*field:].sum(axis=0),required.ravel()):
                masks=rows[found,:field]
                break
        if masks is not None:
            break
    if masks is None:
        print(f"{matches} fingerprint matches, zero solutions")
        return
    seq = []
    for row in masks:
        signs = []
        for i,j,a,b in np.ndindex(7,19,3,3):
            if field == 3:
                t = 0 if a == b == 0 else 1 if (a == 0 or b == 0) else 2
            else:
                t = int(a != 0) + 2*int(b != 0)
            signs.append("-" if row[t] >> labels[i,j] & 1 else "+")
        seq.append("".join(signs))
    save_signs(seq,output)


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("shape",type=Path)
    parser.add_argument("field",choices=("qr","klein"))
    parser.add_argument("rows",type=Path)
    parser.add_argument("library",type=Path)
    parser.add_argument("output",type=Path)
    args=parser.parse_args()
    solve(args.shape,args.field,args.rows,args.library,args.output)

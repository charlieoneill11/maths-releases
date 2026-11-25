"""Enumerate the field-trivial solutions for a fixed allocation and row-sum pattern."""
import argparse
from itertools import product
import json
from pathlib import Path
import sys
import time

import numpy as np

from joint import orbit_table


def block_list(shape, spec, normalize_all, reps, labels, enum_pattern, block_spec):
    n,m,sigma,epsilon = spec
    S,E = enum_pattern(shape,n,m,sigma,epsilon,cansign=False)
    u = S[:,reps].astype(np.int16) + 9*E[:,reps]
    # The six possible u values determine both s and e. Encode lexicographic
    # order on 17 symbols using 51 bits, with no hash-collision risk.
    rank = np.searchsorted([-9,-7,-1,1,7,9],u)
    radix = 8**np.arange(len(reps)-1,-1,-1,dtype=np.int64)
    key = rank @ radix
    keep = np.ones(len(S),dtype=bool)
    units = product(range(1,7),range(1,19)) if normalize_all else [(6,18)]
    i,j = np.unravel_index(reps,(7,19))
    for a,b in units:
        take = labels[(a*i)%7,(b*j)%19]
        keep &= key <= rank[:,take] @ radix
    print(f"block {spec}: {len(S)} exact entries, {int(keep.sum())} representatives",flush=True)
    return block_spec(n,S=S[keep],E=E[keep],cansign=False)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("gs",type=Path)
    parser.add_argument("output",type=Path)
    parser.add_argument("--generator",type=int,choices=(4,5),default=4)
    parser.add_argument("--spec",default="4,1,19,-2:7,4,8,-1:12,3,53,-6:33,0,26,-3")
    args=parser.parse_args()
    sys.path.insert(0,str(args.gs.resolve()))
    from gs_samp import make_shape, enum_pattern
    from gl1 import BlockSpec,L1
    spec=[tuple(map(int,t.split(","))) for t in args.spec.split(":")]
    if len(spec)!=4 or any(len(t)!=4 for t in spec):
        raise ValueError("expected four n,m,sigma,epsilon tuples")
    shape=make_shape("spence",[7,19],9,[[[2,args.generator],1]],None)
    labels,_=orbit_table(args.generator)
    reps=np.array([np.flatnonzero(labels.ravel()==k)[0] for k in range(17)])
    lists=[block_list(shape,t,i==0,reps,labels,enum_pattern,BlockSpec) for i,t in enumerate(spec)]
    # gl1 joins 0+2 against 1+3. Pair the smallest with the largest.
    order=sorted(range(4),key=lambda i:lists[i].L)
    join_order=[order[0],order[1],order[3],order[2]]
    l1=L1(shape)
    now=time.monotonic()
    params=dict(per_class=250000,maxout=50000,hseed=4792)
    count,S,E,_=l1.run([lists[i] for i in join_order],**params)
    if len(S)!=count:
        params["maxout"]=count
        count,S,E,_=l1.run([lists[i] for i in join_order],**params)
    if count!=len(S):
        raise RuntimeError("incomplete first-stage output")
    undo=np.argsort(join_order)
    u=S[:,undo][:,:,reps]+9*E[:,undo][:,:,reps]
    np.savez_compressed(args.output,u=u,spec=np.array(spec),generator=args.generator)
    print(f"{count} first-stage instances, {time.monotonic()-now:.2f} seconds in join",flush=True)


if __name__=="__main__":
    main()

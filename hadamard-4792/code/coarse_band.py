"""Enumerate K-level instances by matching the two axial powers before mixed shifts."""
import argparse
from collections import defaultdict
from itertools import product
from pathlib import Path
import sys
import time

import numpy as np
from band import block_list
from joint import orbit_table
from complete_node import mixed_shifts, shift_counts


def block_groups(u, columns, matrices):
    projected=u.astype(np.int32) @ columns
    powers=[]
    for j,p in ((0,7),(3,19)):
        z,a,b=projected[:,j:j+3].T
        powers.append(((2*z-a-b)**2 + p*(a-b)**2)//4)
    passed=np.flatnonzero(np.maximum(*powers)<=4792)
    groups=defaultdict(list)
    for i in passed:
        groups[int(powers[0][i]),int(powers[1][i])].append(i)
    signatures, coeff = mixed_features(u, matrices)
    hashes=signatures.astype(np.uint64) @ coeff
    return {key: (np.array(ix),hashes[ix]) for key,ix in groups.items()}, signatures, coeff


def mixed_features(u, matrices):
    # A homomorphic fingerprint lets one missed key exclude a pair exactly.
    # Actual sums are checked on all six integer coordinates on every match.
    coeff=np.random.default_rng(1197).bit_generator.random_raw(len(matrices))
    signatures=np.empty((len(u),len(matrices)),dtype=np.int32)
    for k in range(0,len(u),4096):
        x=u[k:k+4096].astype(np.int16)
        signatures[k:k+4096]=np.column_stack([((x @ m)*x).sum(axis=1) for m in matrices])
    return signatures, coeff


def group_patterns(groups):
    pairs=defaultdict(list)
    for a,b in product(groups[0],groups[1]):
        p,q=a[0]+b[0],a[1]+b[1]
        if max(p,q)<=4792:
            pairs[p,q].append((a,b))
    for c,d in product(groups[2],groups[3]):
        want=4792-c[0]-d[0],4792-c[1]-d[1]
        for a,b in pairs.get(want,()):
            yield a,b,c,d


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("gs",type=Path)
    parser.add_argument("output",type=Path)
    parser.add_argument("--generator",type=int,choices=(4,5),default=4)
    parser.add_argument("--spec",default="6,0,1,0:18,0,1,0:18,0,1,0:18,18,1,0")
    parser.add_argument("--count-only",action="store_true")
    parser.add_argument("--library",type=Path)
    parser.add_argument("--start",type=int,default=0)
    parser.add_argument("--stop",type=int)
    args=parser.parse_args()
    sys.path.insert(0,str(args.gs.resolve()))
    from gs_samp import make_shape,enum_pattern
    from gl1 import BlockSpec
    from complete_node import find_match
    if args.library:
        from native_join import Join
        find_match=Join(args.library)
    spec=[tuple(map(int,t.split(","))) for t in args.spec.split(":")]
    if len(spec)!=4 or any(len(t)!=4 for t in spec):
        raise ValueError("expected four n,m,sigma,epsilon tuples")
    labels,columns=orbit_table(args.generator)
    shifts=mixed_shifts(args.generator)
    mats=shift_counts(labels,shifts)
    reps=np.array([np.flatnonzero(labels.ravel()==k)[0] for k in range(17)])
    shape=make_shape("spence",[7,19],9,[[[2,args.generator],1]],None)
    pools=[]
    groups=[]
    sigs=[]
    for i,term in enumerate(spec):
        block=block_list(shape,term,i==0,reps,labels,enum_pattern,BlockSpec)
        u=block.S[:,reps]+9*block.E[:,reps]
        del block
        g,v,coeff=block_groups(u,columns,mats)
        pools.append(u)
        groups.append(g)
        sigs.append(v)
    target=np.full(6,-36,dtype=np.int32)
    wanted=target.astype(np.uint64) @ coeff
    # Include the K-origin equation when the supplied allocation is arbitrary.
    if sum(10*n-4*m for n,m,sg,ep in spec)!=528 or any(abs(sg+9*ep)!=1 for n,m,sg,ep in spec):
        raise ValueError("inconsistent allocation or Spence row sums")
    patterns=sorted(group_patterns(groups))
    total=0
    samples=[]
    now=time.monotonic()
    for pat in patterns[args.start:args.stop]:
        gs=[group[p] for group,p in zip(groups,pat)]
        lengths=sorted(len(x[0]) for x in gs)
        total+=lengths[0]*lengths[3]+lengths[1]*lengths[2]
        if args.count_only:
            continue
        candidates=[(hashes,ix) for ix,hashes in gs]
        for ids in find_match(candidates,wanted):
            if np.array_equal(sum(v[i] for v,i in zip(sigs,ids)),target):
                samples.append(np.stack([u[i] for u,i in zip(pools,ids)]))
    print(f"{len(patterns)} axial class tuples overall; selected pair work {total}; "
          f"{len(samples)} instances returned in {time.monotonic()-now:.2f}s",flush=True)
    if not args.count_only:
        data=np.array(samples,dtype=np.int8).reshape(-1,4,17)
        np.savez_compressed(args.output,u=data,spec=np.array(spec),generator=args.generator)


if __name__=="__main__":
    main()

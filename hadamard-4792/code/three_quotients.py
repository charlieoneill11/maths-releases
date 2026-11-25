"""Starting at a K-level solution, search for signs satisfying both other pair quotients."""
import argparse
from itertools import product
import json
from pathlib import Path
import sys

import numpy as np

from joint import orbit_table
from lift import field_array, paf_check


def signatures(s, e, columns, weights):
    active = np.flatnonzero(e == 0)
    ids = np.arange(1 << len(active))
    t = np.zeros((len(ids),len(s)), dtype=np.int16)
    t[:,active] = 2*((ids[:,None] >> np.arange(len(active))) & 1)-1
    sm = s @ columns
    tm = t @ columns
    tau = t @ weights
    powers = []
    for p, start in ((7,0),(19,3)):
        for sign in (-1,1):
            z,a,b = (sm[start:start+3] + sign*3*tm[:,start:start+3]).T.astype(np.int32)
            powers.append(((2*z-a-b)**2+p*(a-b)**2)//4)
    powers = np.stack(powers, axis=1)
    sg = int(s @ weights)
    good = (powers.max(axis=1) <= 4792) & ((abs(sg)+3*abs(tau))**2 <= 4792)
    result = {}
    for total in np.unique(tau[good]):
        pos = np.flatnonzero(good & (tau == total))
        vals, first = np.unique(powers[pos], axis=0, return_index=True)
        result[int(total)] = vals, t[pos[first]]
    return sg, result


def pair_key(v):
    # Two 14-bit coordinates per word would be enough. Four 14-bit coordinates fit
    # in 56 bits. Each pair sum is below 2^14, so addition is carry-free.
    return v.astype(np.int64) @ (1 << (14*np.arange(4)))


def find_projected(s, e, columns, weights):
    families = [signatures(x,y,columns,weights) for x,y in zip(s,e)]
    # Squaring in int16 would overflow before a single-block cut for extreme
    # inputs. All retained sums below are computed as Python integers.
    dim = [f[0] for f in families]
    groups = [f[1] for f in families]
    for ts in product(*(g.keys() for g in groups)):
        if sum((x+3*y)**2 for x,y in zip(dim,ts)) != 4792:
            continue
        if sum((x-3*y)**2 for x,y in zip(dim,ts)) != 4792:
            continue
        levels = [g[v] for g,v in zip(groups,ts)]
        smallest = sorted(range(4),key=lambda j:len(levels[j][0]))
        pairs = [(smallest[0],smallest[3]),(smallest[1],smallest[2])]
        pairs.sort(key=lambda p:len(levels[p[0]][0])*len(levels[p[1]][0]))
        (a,b),(c,d) = pairs
        # If four bounded powers sum to target coordwise, their packed keys sum to
        # this target. Confirm actual component equality on any match.
        keys = [pair_key(g[0]) for g in levels]
        left = (keys[a][:,None]+keys[b]).ravel()
        ix = np.argsort(left)
        left = left[ix]
        want = pair_key(np.full(4,4792))-(keys[c][:,None]+keys[d]).ravel()
        lo = np.searchsorted(left,want)
        hits = np.flatnonzero(left[np.minimum(lo,len(left)-1)] == want)
        for pos in hits:
            k,l = divmod(int(pos), len(keys[d]))
            for h in ix[lo[pos]:np.searchsorted(left,want[pos],side="right")]:
                i,j = divmod(int(h),len(keys[b]))
                choices = [None]*4
                for row,index in ((a,i),(b,j),(c,k),(d,l)):
                    choices[row]=index
                if np.all(sum(g[0][i] for g,i in zip(levels,choices)) == 4792):
                    return [g[1][i] for g,i in zip(levels,choices)]
    return None


def check_three(arrays):
    if arrays.shape != (4,7,19,3,3) or not np.all(abs(arrays)==1):
        raise ValueError("invalid sign array")
    for axis,kernel in ((1,7),(2,19),((3,4),9)):
        compressed = arrays.sum(axis=axis)
        paf_check(compressed,lambda shift: (4792 if not any(shift) else 0)-4*kernel)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("upstream_gs",type=Path)
    parser.add_argument("--rounds",type=int,default=10)
    parser.add_argument("--seed",type=int,default=479204)
    parser.add_argument("--start",type=int,default=0)
    parser.add_argument("--output",type=Path,required=True)
    args = parser.parse_args()
    sys.path.insert(0,str(args.upstream_gs.resolve()))
    from gs_samp import make_shape, parse_allocs
    from gl1 import L1
    from prod_5912 import level1, dedupe
    shape=make_shape("spence",[7,19],9,[[[2,4],1]],None)
    l1=L1(shape)
    allocation=parse_allocs("4.1:7.4:12.3:33.0",1500,80000)
    cache={}
    labels,columns=orbit_table(4)
    reps=np.array([np.flatnonzero(labels.ravel()==k)[0] for k in range(len(columns))])
    weights=np.bincount(labels.ravel()).astype(np.int32)
    checked=0
    for rd in range(args.start,args.start+args.rounds):
        rng=np.random.default_rng([args.seed,rd])
        _,_,S,E=level1(shape,l1,allocation,cache,rng,rd,maxinst=40)
        keep=dedupe(shape,S,E)
        for i in keep:
            s,e=S[i][:,reps].astype(np.int32),E[i][:,reps].astype(np.int32)
            ts=find_projected(s,e,columns,weights)
            checked+=1
            if ts is None:
                continue
            sheets=np.stack((s+e,e+ts,e-ts),axis=-1)
            arrays=np.array([field_array(block,labels) for block in sheets])
            check_three(arrays)
            cert=dict(seed=args.seed,round=rd,instance=int(i),generator=4,
                      sheets=sheets.tolist(),first_stage_instances_tested=checked)
            args.output.write_text(json.dumps(cert)+"\n")
            print(f"three projections jointly verified after {checked} first-stage instances",flush=True)
            return
        print(f"round {rd}: {len(keep)} representatives, cumulative {checked}",flush=True)


if __name__ == "__main__":
    main()

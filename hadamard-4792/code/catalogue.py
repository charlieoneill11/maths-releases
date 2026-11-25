"""List all tau-feasible normalized allocation/row-sum bands and exact individual sizes."""
import argparse
from collections import defaultdict
from functools import lru_cache
from itertools import product
import json
from math import comb, log10
from pathlib import Path
import sys


@lru_cache(maxsize=None)
def list_size(spec):
    n,m,sigma,epsilon=spec
    # Entries record n, m, s, e for one orbit. K has three light orbits
    # with weights 1,3,3 and fourteen heavy orbits with weight 9.
    letters=((0,0,1,0),(0,0,-1,0),(1,0,0,1),(1,0,0,-1),(1,1,-2,1),(1,1,2,-1))
    total=0
    for a,b,c in product(letters,repeat=3):
        residue=[x-y-3*z-3*w for x,y,z,w in zip(spec,a,b,c)]
        if any(r%9 for r in residue):
            continue
        nh,mh,sh,eh=[r//9 for r in residue]
        plain,opposed,regular=nh-mh,mh,14-nh
        if min(plain,opposed,regular)<0 or (eh+nh)%2:
            continue
        for opp_plus in range(opposed+1):
            plain_plus=(eh+nh)//2-opp_plus
            numerator=sh+regular+4*opp_plus-2*opposed
            reg_plus=numerator//2
            if numerator%2 or not 0<=plain_plus<=plain or not 0<=reg_plus<=regular:
                continue
            total+=(comb(14,plain)*comb(14-plain,opposed)*comb(plain,plain_plus)
                    *comb(opposed,opp_plus)*comb(regular,reg_plus))
    return total


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("gs",type=Path)
    parser.add_argument("output",type=Path)
    parser.add_argument("--generator",type=int,choices=(4,5),default=4)
    parser.add_argument("--estimates",type=Path)
    args=parser.parse_args()
    sys.path.insert(0,str(args.gs.resolve()))
    from gs_samp import make_shape
    from tau_patterns import patterns
    sh=make_shape("spence",[7,19],9,[[[2,args.generator],1]],None)
    (features,_,inverse,states),_=patterns(sh)
    buckets=defaultdict(set)
    for f,st in zip(inverse,states):
        n,m,s,rho,t=map(int,st)
        e=(rho-s)//9
        if s<0 or (s==0 and e<0):
            s,e=-s,-e
        buckets[int(f)].add((n,m,s,e))
    bands=set()
    for feat in features:
        for rows in product(*(buckets[f] for f in feat)):
            bands.add(tuple(sorted(rows)))
    estimates={}
    if args.estimates:
        for row in json.loads(args.estimates.read_text()):
            estimates[tuple(row["alloc"])]=(row["logE"],row["logN1"])
    result=[]
    for rows in sorted(bands):
        sizes=[list_size(spec) for spec in rows]
        if not all(sizes):
            raise ValueError("inconsistent row enumeration")
        # Global multipliers may be used to normalize any ONE block.
        order=sorted(range(4),key=lambda k:(sizes[k],rows[k]))
        normalized=[rows[k] for k in order]
        counts=[sizes[k] for k in order]
        alloc=tuple(sorted(r[0] for r in rows))
        result.append(dict(spec=normalized,sizes=counts,estimate=estimates.get(alloc)))
    args.output.write_text(json.dumps(result,separators=(",",":"))+"\n")
    print(f"{len(result)} normalized bands, {list_size.cache_info().currsize} single-block types")


if __name__=="__main__":
    main()

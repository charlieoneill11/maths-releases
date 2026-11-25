"""Exact prime-field quotient screen conditioned on defects and all row sums."""
import argparse
from collections import defaultdict
from functools import lru_cache
from itertools import product
import json
from pathlib import Path

from quotient import profiles


def row_options(weights):
    # For each orbit in one fibre choose its three independent signs.
    dp={(0,0,0,0,0)}
    signs=list(product((-1,1),repeat=3))
    for w in weights:
        dp={(a+w*x,b+w*y,c+w*z,n+w*(y==z),m+w*(x!=y and y==z))
            for a,b,c,n,m in dp for x,y,z in signs}
    groups=defaultdict(list)
    for a,b,c,n,m in dp:
        groups[a,b,c].append((n,m))
    return groups


def bank(p, types):
    zero,other=(([1,3,3],[1]*7) if p==19 else ([1,9,9],[1]+[3]*6))
    fixed=row_options(zero)
    nonzero=row_options(other)
    h=(p-1)//2
    spectra,_=profiles(p,retain_all=True)
    result=defaultdict(lambda:defaultdict(set))
    for (u,v),powers in spectra.items():
        sigma=(u+v)//2
        epsilon=(1-sigma)//9
        tau=(u-v)//6
        if sigma<0 or (sigma==0 and epsilon<0):
            sigma,epsilon,tau=-sigma,-epsilon,-tau
        for norms,rows in powers.items():
            for r0,ra,rb in rows:
                for a,b,c in product(fixed[r0],nonzero[ra],nonzero[rb]):
                    n=a[0]+h*(b[0]+c[0])
                    m=a[1]+h*(b[1]+c[1])
                    key=(n,m,sigma,epsilon)
                    if key in types:
                        result[key][tau].add(norms)
    # A pair sum fits in each 14-bit digit (at most 9584).
    return {spec:{t:frozenset((a<<28)+(b<<14)+c for a,b,c in norms)
                  for t,norms in entries.items()} for spec,entries in result.items()}


def has_match(groups):
    a,b,c,d=sorted(groups,key=len)
    target=(4792<<28)+(4792<<14)+4792
    # Buckets encode all three powers exactly on each side. A false
    # carry from summing all four is impossible: a carried digit would
    # require 4792 + 16384 > 4*4792 in that coordinate.
    pairs={x+y for x in a for y in d}
    return any(target-x-y in pairs for x in b for y in c)


def screen(records):
    specs=sorted({tuple(row) for band in records for row in band["spec"]})
    b7=bank(7,set(specs))
    b19=bank(19,set(specs))
    print(f"catalogue has {len(specs)} single-block types; {len(b7)} reach 7 x 9 and {len(b19)} reach 19 x 9",flush=True)
    @lru_cache(maxsize=100000)
    def test(p,tag):
        pool=b7 if p==7 else b19
        return has_match([pool[row][t] for row,t in tag])
    survivors=[]
    for band in records:
        rows=[tuple(row) for row in band["spec"]]
        times=[sorted(set(b7.get(r,())).intersection(b19.get(r,()))) for r in rows]
        found=[]
        for ts in product(*times):
            # The nonsquare-field automorphism negates all four tau values.
            if next((t for t in ts if t),0)<0:
                continue
            if sum((s[2]+3*t)**2 for s,t in zip(rows,ts))!=4792:
                continue
            if sum((s[2]-3*t)**2 for s,t in zip(rows,ts))!=4792:
                continue
            tag=tuple(sorted(zip(rows,ts)))
            if test(19,tag) and test(7,tag):
                found.append(ts)
        if found:
            survivors.append(dict(**band,tau=found))
    return survivors


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("catalogue",type=Path)
    parser.add_argument("output",type=Path)
    args=parser.parse_args()
    records=json.loads(args.catalogue.read_text())
    alive=screen(records)
    args.output.write_text(json.dumps(alive,separators=(",",":"))+"\n")
    print(f"{len(alive)} of {len(records)} bands survive both prime-field quotients with common tau, "
          f"{sum(len(r['tau']) for r in alive)} passing ordered tau patterns up to overall sign")

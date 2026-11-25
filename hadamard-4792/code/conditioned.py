"""Search a normalized band after conditioning its K-level join on both field quotients."""
import argparse
from collections import defaultdict
from itertools import product
import json
from pathlib import Path
import sys
import time

import numpy as np
from band import block_list
from coarse_band import mixed_features
from complete_node import mixed_shifts, shift_counts
from joint import orbit_table
from native_join import Join
from quotient import profiles
from screen import row_options


def row_code(u,s,n,m):
    # u fits in [-171,171], s in [-38,38], n,m in [0,19].
    return (((u+171)*77+(s+38))*20+n)*20+m


def ordered_key(rows):
    return rows[0],min(rows[1:]),max(rows[1:])


def spectral_tables(p, types):
    zero,other=(([1,3,3],[1]*7) if p==19 else ([1,9,9],[1]+[3]*6))
    fixed,nonzero=row_options(zero),row_options(other)
    powers,_=profiles(p,retain_all=True)
    h=(p-1)//2
    data=defaultdict(lambda:defaultdict(lambda:defaultdict(set)))
    for (u,v),table in powers.items():
        s=(u+v)//2
        e=(1-s)//9
        tau=(u-v)//6
        gauge=-1 if s<0 or (s==0 and e<0) else 1
        s,e,tau=gauge*s,gauge*e,gauge*tau
        if (s,e) not in {r[2:] for r in types}:
            continue
        for norms,boards in table.items():
            key=(norms[0]<<28)+(norms[1]<<14)+norms[2]
            for board in boards:
                us=[gauge*(a+4*b+4*c) for a,b,c in board]
                ss=[gauge*(a-(b+c)//2) for a,b,c in board]
                options=[fixed[board[0]],nonzero[board[1]],nonzero[board[2]]]
                for a,b,c in product(*options):
                    n=a[0]+h*(b[0]+c[0])
                    m=a[1]+h*(b[1]+c[1])
                    spec=(n,m,s,e)
                    if spec in types:
                        code=ordered_key([row_code(x,y,*w) for x,y,w in zip(us,ss,(a,b,c))])
                        data[spec][tau][key].add(code)
    return data


def matches(groups):
    target=(4792<<28)+(4792<<14)+4792
    left=defaultdict(list)
    for a,b in product(*groups[:2]):
        left[a+b].append((a,b))
    for c,d in product(*groups[2:]):
        for a,b in left.get(target-c-d,()):
            yield a,b,c,d


def margins(u, columns):
    e=np.where(abs(u)>1,np.sign(u),0)
    s=u-9*e
    arrays=[a.astype(np.int32) @ columns for a in (u,s,e!=0,s*e==-2)]
    # Promote to int64 before packing.
    values=row_code(*(a.astype(np.int64) for a in arrays))
    for offset in (0,3):
        values[:,offset+1:offset+3].sort(axis=1)
    return values


def assign(units, tables, needed):
    # Invert each mapping from power signature to compressed row types.
    reverse=[]
    for norm_table,keys in zip(tables,needed):
        bytype=defaultdict(list)
        for key in keys:
            for kind in norm_table[key]:
                bytype[kind].append(key)
        reverse.append(bytype)
    indices=defaultdict(list)
    for key,ix in units:
        for pair in product(reverse[0].get(key[:3],()),reverse[1].get(key[3:],())):
            indices[pair].append(ix)
    return {pair:np.concatenate(chunks) for pair,chunks in indices.items()}


def ordered_groups(compressions):
    vals,inv=np.unique(compressions,axis=0,return_inverse=True)
    inv=inv.ravel()
    ix=np.argsort(inv)
    boundaries=np.r_[0,np.cumsum(np.bincount(inv))]
    return [(tuple(map(int,v)),ix[boundaries[j]:boundaries[j+1]]) for j,v in enumerate(vals)]


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("gs",type=Path)
    parser.add_argument("survivors",type=Path)
    parser.add_argument("output",type=Path)
    parser.add_argument("library",type=Path)
    parser.add_argument("--index",type=int,required=True)
    parser.add_argument("--margin-library",type=Path)
    parser.add_argument("--generator",type=int,choices=(4,5),default=4)
    parser.add_argument("--combine",action=argparse.BooleanOptionalAction,default=True)
    parser.add_argument("--plan-only",action="store_true")
    parser.add_argument("--rayleigh",action=argparse.BooleanOptionalAction,default=True)
    args=parser.parse_args()
    sys.path.insert(0,str(args.gs.resolve()))
    band=json.loads(args.survivors.read_text())[args.index]
    specs=[tuple(x) for x in band["spec"]]
    tables=[spectral_tables(p,set(specs)) for p in (7,19)]
    labels,columns=orbit_table(args.generator)
    mats=shift_counts(labels,mixed_shifts(args.generator))
    reps=np.array([np.flatnonzero(labels.ravel()==k)[0] for k in range(17)])
    plans=[]
    allowed=[[set(),set()] for _ in specs]
    for ts in band["tau"]:
        by_prime=[[tab[sp][t] for sp,t in zip(specs,ts)] for tab in tables]
        viable=[list(matches(g)) for g in by_prime]
        plans.append((by_prime,viable))
        for j in range(2):
            for i in range(4):
                for key in {m[i] for m in viable[j]}:
                    allowed[i][j].update(by_prime[j][i][key])
    generator=None
    if args.margin_library:
        from margin_blocks import MarginBlocks
        generator=MarginBlocks(args.margin_library,labels)
    else:
        from gl1 import BlockSpec
        from gs_samp import make_shape,enum_pattern
        shape=make_shape("spence",[7,19],9,[[[2,args.generator],1]],None)
    if args.rayleigh:
        from rayleigh import coefficients,within
        tests=coefficients(labels,mixed_shifts(args.generator))
    pools,hashes,features,types=[],[],[],[]
    for i,sp in enumerate(specs):
        if generator is None:
            block=block_list(shape,sp,i==0,reps,labels,enum_pattern,BlockSpec)
            u=block.S[:,reps]+9*block.E[:,reps]
            del block
        else:
            u=generator.generate(allowed[i],i==0)
            print(f"block {sp}: {len(u)} representatives within permitted margins",flush=True)
        if args.rayleigh:
            size=len(u)
            u=within(u,tests)
            print(f"integral character bounds retain {len(u)}/{size} K-blocks",flush=True)
        sig,coeff=mixed_features(u,mats)
        hashes.append(sig.astype(np.uint64) @ coeff)
        features.append(sig)
        pools.append(u)
        types.append(ordered_groups(margins(u,columns)))
    if generator is not None:
        generator.close()
    target=np.full(6,-36,dtype=np.int32)
    wanted=target.astype(np.uint64) @ coeff
    join=Join(args.library)
    answers=set()
    visited=set()
    total=0
    now=time.monotonic()
    def original_jobs():
        for by_prime,viable in plans:
            cols=[]
            for i in range(4):
                used=[{x[i] for x in patterns} for patterns in viable]
                cols.append(assign(types[i],[g[i] for g in by_prime],used))
            for a,b in product(*viable):
                bucket=[cols[i].get(pair) for i,pair in enumerate(zip(a,b))]
                if any(ix is None for ix in bucket):
                    continue
                yield bucket
    if args.combine:
        from plan_buckets import build
        columns,jobs,total=build(types,plans)
        if args.plan_only:
            return
        batches=([col.data(k) for col,k in zip(columns,job)] for job in jobs)
    else:
        batches=original_jobs()
    for bucket in batches:
        if not args.combine:
            sizes=sorted(map(len,bucket))
            total+=sizes[0]*sizes[3]+sizes[1]*sizes[2]
        groups=[(x[ix],ix) for x,ix in zip(hashes,bucket)]
        for ids in join(groups,wanted):
            key=tuple(map(int,ids))
            if key in visited:
                continue
            visited.add(key)
            if np.array_equal(sum(x[i] for x,i in zip(features,ids)),target):
                answers.add(key)
    data=np.array([[u[i] for u,i in zip(pools,row)] for row in sorted(answers)],
                  dtype=np.int8).reshape(-1,4,17)
    np.savez_compressed(args.output,u=data,spec=np.array(specs),generator=args.generator)
    print(f"{total} paired entries, {len(data)} K-level instances after the conditioned join "
          f"in {time.monotonic()-now:.2f}s",flush=True)


if __name__=="__main__":
    main()

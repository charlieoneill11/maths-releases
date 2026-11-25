"""Stream the field-DC classes and count the exact surviving four-row jobs."""
import argparse
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np


def dc_rows(data,field,runs=None):
    counts=Counter()
    for first in range(0,len(data),65536):
        batch=data[first:first+65536,field+1:2*field]
        # Generation visits each tuple of sheet sums together.
        at=np.r_[0,np.flatnonzero(np.any(batch[1:]!=batch[:-1],axis=1))+1,len(batch)]
        for j in range(len(at)-1):
            key=tuple(map(int,batch[at[j]]))
            counts[key]+=int(at[j+1]-at[j])
            if runs is not None:
                runs[key].append((first+at[j],first+at[j+1]))
    return counts


def dc_plans(counts):
    keys=list(counts)
    pairs=defaultdict(list)
    for j,b in enumerate(keys):
        for i,a in enumerate(keys[:j+1]):
            total=tuple(x+y for x,y in zip(a,b))
            if max(total)<=4792:
                pairs[total].append((i,j))
    jobs=set()
    for total,group in pairs.items():
        other=pairs.get(tuple(4792-x for x in total),())
        for a,b in group:
            for c,d in other:
                jobs.add(tuple(sorted((a,b,c,d))))
    work=used=0
    active={i for job in jobs for i in job}
    for i in active:
        used+=counts[keys[i]]
    for job in jobs:
        a,b,c,d=sorted(counts[keys[i]] for i in job)
        work+=a*d+b*c
    print(f"{sum(counts.values())} rows in {len(keys)} field classes, {len(jobs)} field tuples, "
          f"{used} usable rows in {len(active)} classes, {work} pair entries before additional screens",flush=True)
    return keys,jobs


def open_rows(shape,name,path):
    k,lags=map(int,shape.read_text().splitlines()[0].split())
    field=3 if name=="qr" else 4
    width=field*(2+lags)
    if path.stat().st_size% (4*width):
        raise ValueError("partial native row file")
    data=np.memmap(path,dtype=np.int32,mode="r").reshape(-1,width) if path.stat().st_size else np.empty((0,width),np.int32)
    return data,field,lags


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("shape",type=Path)
    parser.add_argument("field",choices=("qr","klein"))
    parser.add_argument("rows",type=Path)
    args=parser.parse_args()
    data,field,lags=open_rows(args.shape,args.field,args.rows)
    dc_plans(dc_rows(data,field))

"""Plant a known target fingerprint and check that phase.cpp reaches its exact verifier."""
import argparse
import ctypes as ct
import json
from pathlib import Path

import numpy as np
from joint import orbit_table


def coefficients():
    mask=(1<<64)-1
    state=4792
    while True:
        state=(state+0x9e3779b97f4a7c15)&mask
        w=state
        w=((w^(w>>30))*0xbf58476d1ce4e5b9)&mask
        w=((w^(w>>27))*0x94d049bb133111eb)&mask
        yield w^(w>>31)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("library",type=Path)
    parser.add_argument("data",type=Path)
    args=parser.parse_args()
    data=json.loads(args.data.read_text())
    labels,_=orbit_table(data["generator"])
    labels=labels.astype(np.int16)
    a,b,c=np.array(data["sheets"]).transpose(2,0,1)
    e=(b+c)//2
    s,t=a-e,(b-c)//2
    u=np.ascontiguousarray(s+9*e,dtype=np.int8)
    s=s[:,labels]
    t=t[:,labels]
    first=next((int(x) for x in t.sum(axis=(1,2)) if x),0)
    if first<0:
        t=-t
    rng=coefficients()
    fingerprint=0
    for i,j in np.ndindex(7,19):
        sr=np.roll(s,(i,j),(1,2))
        tr=np.roll(t,(i,j),(1,2))
        auto=int((s*sr+9*t*tr).sum())
        cross=int((t*sr+s*tr).sum())
        fingerprint+=next(rng)*auto+next(rng)*cross
    lib=ct.CDLL(str(args.library.resolve()))
    lib.planted_phase.argtypes=[ct.c_void_p,ct.c_void_p,ct.c_uint64,ct.c_void_p]
    lib.planted_phase.restype=ct.c_int
    counts=np.zeros(4,dtype=np.uint64)
    result=lib.planted_phase(labels.ctypes.data,u.ctypes.data,fingerprint%(1<<64),counts.ctypes.data)
    if result!=0 or counts[2]<1:
        raise ValueError(f"failed planted control: status {result}, counters {counts}")
    print(f"known projected solution reached the exact verifier, {counts[2]} fingerprint matches; "
          "full correlation verification rejected it")


if __name__=="__main__":
    main()

"""Exact staged integer search of the free t signs for each K-level input."""
import argparse
import ctypes as ct
import json
from pathlib import Path
import time

import numpy as np
from joint import orbit_table
from lift import field_array, paf_check


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("library",type=Path)
    parser.add_argument("band",type=Path)
    parser.add_argument("--start",type=int,default=0)
    parser.add_argument("--stop",type=int)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--canonical",action=argparse.BooleanOptionalAction,default=True)
    args=parser.parse_args()
    lib=ct.CDLL(str(args.library.resolve()))
    ptr=ct.c_void_p
    lib.create_phase.argtypes=[ptr]
    lib.create_phase.restype=ptr
    lib.phase_batch.argtypes=[ptr,ptr,ct.c_int,ptr,ptr]
    lib.phase_batch.restype=ct.c_int
    lib.delete_phase.argtypes=[ptr]
    lib.delete_phase.restype=None
    data=np.load(args.band)
    u=np.ascontiguousarray(data["u"][args.start:args.stop],dtype=np.int8)
    labels,_=orbit_table(int(data["generator"]))
    labels=np.ascontiguousarray(labels,dtype=np.int16)
    selected=None
    if args.canonical:
        from orbit_reduce import representatives
        selected=representatives(u,labels)
        print(f"{len(u)} K-level instances, {len(selected)} after scalar, reversal, sign and permutation reductions",flush=True)
        u=np.ascontiguousarray(u[selected])
    engine=lib.create_phase(labels.ctypes.data)
    if not engine:
        raise RuntimeError("native engine setup failed")
    counts=np.zeros(4,dtype=np.uint64)
    masks=np.zeros(4,dtype=np.uint32)
    start=time.perf_counter()
    try:
        for i in range(0,len(u),128):
            part=u[i:i+128]
            which=lib.phase_batch(engine,part.ctypes.data,len(part),masks.ctypes.data,counts.ctypes.data)
            if which < -1:
                raise RuntimeError("native search failed")
            if which>=0:
                chosen=part[which]
                e=np.where(abs(chosen)>1,np.sign(chosen),0)
                s=chosen-9*e
                t=np.where(e==0,2*((masks.astype(np.int64)[:,None]>>np.arange(17))&1)-1,0)
                signs=np.stack((s+e,e+t,e-t),axis=-1)
                arrays=np.array([field_array(x,labels) for x in signs])
                if not np.all(abs(arrays)==1):
                    raise RuntimeError("non-sign lift")
                paf_check(arrays,lambda h:(4792 if not any(h) else 0)-4)
                cert=dict(order=4792,construction="spence",group=[7,19,3,3],
                          sequences=["".join("+" if v==1 else "-" for v in x.flat) for x in arrays])
                args.output.write_text(json.dumps(cert)+"\n")
                original=int(selected[i+which]) if selected is not None else i+which
                print(f"full witness at record {args.start+original}",flush=True)
                return
            if i and i%2048==0:
                print(f"finished {i+len(part)}/{len(u)} instances",flush=True)
    finally:
        lib.delete_phase(engine)
    print(f"{len(u)} instances, {counts[0]} row-sum tuples, {counts[1]} projected class matches, "
          f"{counts[2]} full hash matches, no solution; {time.perf_counter()-start:.3f}s",flush=True)


if __name__=="__main__":
    main()

"""Finish an exact K-level band using Kumar's integer mode with PSD pruning disabled."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

import numpy as np
from joint import orbit_table
from lift import field_array, paf_check


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("gs",type=Path)
    parser.add_argument("band",type=Path)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--omit",default="")
    args=parser.parse_args()
    gs=args.gs.resolve()
    sys.path.insert(0,str(gs))
    from gs_samp import make_shape
    from gl2io import header_text, instance_text
    data=np.load(args.band)
    generator=int(data["generator"])
    labels,_=orbit_table(generator)
    u=data["u"].astype(np.int16)
    e=np.where(abs(u)>1,np.sign(u),0)
    s=u-9*e
    shape=make_shape("spence",[7,19],9,[[[2,generator],1]],None)
    header,nch=header_text(shape)
    binary=gs/("gl2n_32" if nch<=32 else "gl2n_64")
    env=dict(os.environ,GL2_NOPSD="1",GL2_OMIT=args.omit,GL2_NMCAP="0")
    total=near=rejected=0
    for start in range(0,len(s),64):
        size=min(64,len(s)-start)
        with tempfile.TemporaryDirectory() as temp:
            path=Path(temp)/"input"
            with path.open("w") as out:
                out.write(header+f"{size}\n")
                for i in range(start,start+size):
                    out.write(instance_text(shape,[(sb[labels.ravel()],eb[labels.ravel()])
                                                  for sb,eb in zip(s[i],e[i])]))
            run=subprocess.run([str(binary),str(path),"1","1e9","4792","1500000","0"],
                               env=env,capture_output=True,text=True,check=True)
        lines=run.stdout.splitlines()
        statuses=[line for line in lines if line.startswith("INST ")]
        if len(statuses)!=size or any("TIMEOUT" in line or "TOOBIG" in line for line in statuses):
            raise RuntimeError("incomplete second-stage search")
        total+=sum(int(line.split("=")[-1]) for line in lines if line.startswith("TOTAL completions="))
        rejected+=sum("rowfilter" in line for line in statuses)
        near+=sum(int(line.split()[-1]) for line in lines if line.startswith("NMTOT "))
        for line in lines:
            if line.startswith("SOL "):
                columns=line.split("|")
                i=start+int(columns[0].split()[1])
                ts=[np.array(list(map(int,col.split()))) for col in columns[1:5]]
                # The producer emits t for all 133 K-positions, in mixed-radix order.
                arrays=[]
                for sb,eb,t in zip(s[i],e[i],ts):
                    rep=np.array([np.flatnonzero(labels.ravel()==o)[0] for o in range(17)])
                    sheets=np.stack((sb+eb,eb+t[rep],eb-t[rep]),axis=-1)
                    arrays.append(field_array(sheets,labels))
                paf_check(np.array(arrays),lambda shift:(4792 if not any(shift) else 0)-4)
                cert=dict(order=4792,construction="spence",group=[7,19,3,3],
                          sequences=["".join("+" if x==1 else "-" for x in b.ravel()) for b in arrays])
                args.output.write_text(json.dumps(cert)+"\n")
                print("verified a full 4792 certificate",flush=True)
                return
    if total:
        raise RuntimeError("positive count without saved solution")
    print(f"{len(s)} first-stage instances, {rejected} row-filter rejections, "
          f"{near} matches on retained coordinates, {total} full completions",flush=True)


if __name__=="__main__":
    main()

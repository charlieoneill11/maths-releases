"""Resume a deterministic set of normalized bands on the local CPU."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

HERE=Path(__file__).resolve().parent


def fingerprint(band, generator):
    text=json.dumps([band["spec"],band["tau"],generator],sort_keys=True)
    return hashlib.sha256(text.encode()).hexdigest()


def run():
    parser=argparse.ArgumentParser()
    parser.add_argument("gs",type=Path)
    parser.add_argument("survivors",type=Path)
    parser.add_argument("pair_library",type=Path)
    parser.add_argument("phase_library",type=Path)
    parser.add_argument("work",type=Path)
    parser.add_argument("--margin-library",type=Path)
    parser.add_argument("--generator",type=int,choices=(4,5),default=4)
    parser.add_argument("--shard",type=int,default=0)
    parser.add_argument("--shards",type=int,default=1)
    parser.add_argument("--min-list",type=int,default=0)
    parser.add_argument("--max-list",type=int,default=1000000)
    parser.add_argument("--cases",type=int)
    args=parser.parse_args()
    if not 0<=args.shard<args.shards:
        parser.error("shard must be between zero and shards minus one")
    args.work.mkdir(parents=True,exist_ok=True)
    records=json.loads(args.survivors.read_text())
    indices=[i for i,r in enumerate(records)
             if i%args.shards==args.shard and args.min_list<=max(r["sizes"])<=args.max_list]
    def priority(i):
        estimate=records[i].get("estimate")
        score=estimate[0] if estimate and estimate[0] is not None else 0
        return -score,max(records[i]["sizes"]),i
    done=0
    for i in sorted(indices,key=priority):
        label=f"g{args.generator}-case{i}"
        receipt=args.work/(label+".json")
        digest=fingerprint(records[i],args.generator)
        if receipt.exists():
            prior=json.loads(receipt.read_text())
            if prior["band_sha256"]!=digest:
                raise RuntimeError("receipt refers to a different band")
            continue
        if args.cases is not None and done>=args.cases:
            break
        print(f"searching {label}",flush=True)
        with tempfile.TemporaryDirectory(dir=args.work) as tmp:
            band=Path(tmp)/"band.npz"
            env=dict(os.environ,OPENBLAS_NUM_THREADS="1",OMP_NUM_THREADS="1")
            first_cmd=[sys.executable,str(HERE/"conditioned.py"),str(args.gs),str(args.survivors),
                       str(band),str(args.pair_library),"--index",str(i),"--generator",str(args.generator)]
            if args.margin_library:
                first_cmd.extend(["--margin-library",str(args.margin_library)])
            now=time.monotonic()
            first=subprocess.run(first_cmd,text=True,stdout=subprocess.PIPE,check=True,env=env)
            hit=args.work/(label+"-4792-witness.json")
            second_cmd=[sys.executable,str(HERE/"phase.py"),str(args.phase_library),str(band),
                        "--output",str(hit)]
            second=subprocess.run(second_cmd,text=True,stdout=subprocess.PIPE,check=True,env=env)
            result=dict(index=i,generator=args.generator,band_sha256=digest,spec=records[i]["spec"],
                        tau=records[i]["tau"],stage1=first.stdout.splitlines()[-1],
                        stage2=second.stdout.splitlines()[-1],wall_seconds=round(time.monotonic()-now,2),
                        hit=hit.exists())
            temp=Path(tmp)/"receipt.json"
            temp.write_text(json.dumps(result,sort_keys=True)+"\n")
            temp.replace(receipt)
            print(json.dumps(result),flush=True)
            done+=1
            if hit.exists():
                return


if __name__=="__main__":
    run()

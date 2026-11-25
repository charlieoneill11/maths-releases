"""Reproduce all direct product-multiplier exclusions with at most 16 K orbits."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

from multiplier_shapes import closure, orbits, prepare, subgroups


ROOT=Path(__file__).resolve().parent


def energy_wall(group):
    for prime,order in ((7,sum(b==1 for a,b in group)),(19,sum(a==1 for a,b in group))):
        count=(prime-1)//order
        low=min(abs(1+order*(count-2*i)) for i in range(count+1))
        if 4*(1197//prime)*low**2>4792-4*prime:
            return prime,order,low
    return None


def run(work,command):
    import shlex
    command=[str(v) for v in command]
    print(shlex.join(command),flush=True)
    proc=subprocess.run(command,cwd=work,text=True,stdout=subprocess.PIPE,check=True,
                        env=dict(os.environ,OPENBLAS_NUM_THREADS="1",OMP_NUM_THREADS="1"))
    print(proc.stdout.strip(),flush=True)
    return proc.stdout.strip()


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("work",type=Path)
    args=parser.parse_args()
    work=args.work.resolve()
    work.mkdir(parents=True,exist_ok=True)
    comp=os.environ.get("CXX","c++")
    names=("axial_product","product_spence","orbit_spence","klein_seven")
    binaries={name:work/name for name in names}
    for name in names:
        run(work,[comp,"-std=c++17","-O3",ROOT/(name+".cpp"),"-o",binaries[name]])
    lib=work/"pair_join.so"
    run(work,[comp,"-std=c++17","-O3","-shared","-fPIC",ROOT/"pair_join.cpp","-o",lib])
    groups=subgroups()
    small=[g for g in groups if len(orbits(g)[1])<=16]
    minimal=sorted((g for g in small if not any(h<g for h in small)),key=lambda g:(len(g),sorted(g)))
    report=[]
    for index,g in enumerate(minimal):
        labels,parts=orbits(g)
        generators=groups[g]
        shape=work/f"shape-{index}.txt"
        data=prepare((len(parts),sorted(g),generators,labels,parts))
        shape.write_text("".join(" ".join(map(str,line))+"\n" for line in data))
        record=dict(generators=generators,K_orbits=len(parts),K_size=len(g),checks={})
        wall=energy_wall(g)
        for field in ("qr","klein"):
            if wall:
                record["checks"][field]=dict(kernel_prime=wall[0],orbit_size=wall[1],minimum=wall[2])
                continue
            prime=next((p for p,proj in ((7,{a for a,b in g}),(19,{b for a,b in g})) if len(proj)==p-1),None)
            if prime:
                path=work/f"axial-{index}-{field}.txt"
                first=run(work,[binaries["axial_product"],shape,field,prime,path])
                result=run(work,[sys.executable,ROOT/"axial_join.py",path])
                if "0 complementary pair sums" != result.split(", ")[-1] and result!="empty single-block pool":
                    raise ValueError(f"surviving prime quotient: {result}")
            elif g==closure([(2,1),(1,4)]):
                path=work/f"product-{field}.txt"
                first=run(work,[binaries["product_spence"],field,path])
                witness=work/f"product-{field}-witness.json"
                result=run(work,[sys.executable,ROOT/"product_join.py",field,path,lib,witness])
                if "zero solutions" not in result:
                    raise ValueError(f"check the possible witness at {witness}")
            elif g==closure([(6,4)]):
                path=work/f"mixed-{field}.bin"
                if field=="qr":
                    first=run(work,[binaries["orbit_spence"],shape,field,path])
                    result=run(work,[sys.executable,ROOT/"orbit_join.py",shape,field,path,lib,
                                              work/"mixed-qr-witness.json"])
                else:
                    first=run(work,[binaries["klein_seven"],path])
                    result=run(work,[sys.executable,ROOT/"seven_join.py",path,lib])
                if "zero solutions" not in result:
                    raise ValueError("surviving case requires checking")
            else:
                raise ValueError(f"uncovered group {sorted(g)}")
            record["checks"][field]={"enumeration":first,"join":result}
        report.append(record)
    if len(groups)!=50 or len(small)!=24 or len(minimal)!=16:
        raise ValueError("unexpected subgroup census")
    (work/"shape-results.json").write_text(json.dumps(report,indent=2)+"\n")
    print("24 scalar subgroups and both four-element field actions excluded",flush=True)


if __name__=="__main__":
    main()

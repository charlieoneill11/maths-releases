"""Replay a small three-height benchmark; all repeats use the same 24,576 bases."""
import os
from pathlib import Path
import re
import statistics
import subprocess
import tempfile
import time

ROOT=Path(__file__).resolve().parent
STARTS=(3_883_853_300_000,10_000_000_000_000,32_654_400_000_000)
COUNT=8192
REPEATS=7


def build(binary,source,flags):
    subprocess.run(['g++','-O3','-std=c++17',str(ROOT/source),*flags,'-o',str(binary)],check=True)


def benchmark():
    allowed=os.sched_getaffinity(0)
    cpu=sorted(allowed)[len(allowed)//2]
    os.sched_setaffinity(0,{cpu})
    print(f'Pinned CPU {cpu}. Each rate is the median of {REPEATS} runs of {COUNT} bases.')
    print('first, old generator/s, IFMA generator/s, IFMA with GMP/s, end-to-end/s')
    with tempfile.TemporaryDirectory() as work:
        work=Path(work)
        old,fast,replay=[work/s for s in ('old','fast','replay')]
        build(old,'verify_11_5.cpp',['-lgmpxx','-lgmp'])
        build(fast,'fast_power_witness.cpp',['-lgmpxx','-lgmp'])
        build(replay,'check_power_witnesses.cpp',['-DUSE_GMP','-lgmpxx','-lgmp'])
        for first in STARTS:
            args=[str(first),str(first+COUNT-1)]
            times=[[] for _ in range(4)]
            for repeat in range(REPEATS):
                for mode in [(repeat+i)%4 for i in range(4)]:
                    start=time.monotonic()
                    exe=old if mode==0 else fast
                    flags={0:[],1:[],2:['--gmp-check'],3:['--witnesses']}[mode]
                    out=subprocess.run([exe,*args,*flags],capture_output=True,check=True)
                    if mode==3:
                        subprocess.run([replay,*args],input=out.stdout,capture_output=True,check=True)
                        elapsed=time.monotonic()-start
                    else:
                        pattern=r' in ([.\d]+) seconds' if mode==0 else r', seconds ([.\deE+-]+)'
                        elapsed=float(re.search(pattern,out.stderr.decode()).group(1))
                    times[mode].append(elapsed)
            rates=[COUNT/statistics.median(sample) for sample in times]
            print(f'{first}: '+', '.join(f'{r:.0f}' for r in rates),flush=True)
    print('End-to-end includes generating the decimal stream and a separate GMP primality and endpoint replay.')
    print('All times are elapsed on one logical CPU; timings exclude compilation and durable storage.')

if __name__=='__main__':
    benchmark()

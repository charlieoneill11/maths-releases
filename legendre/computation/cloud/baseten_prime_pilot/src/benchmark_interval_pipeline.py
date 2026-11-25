"""Measure whole-job throughput, including storing and independently replaying the certificates."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
import resource
import subprocess
import time
from pathlib import Path

LOW_START = 3_883_854_444_452
HIGH_END = 32_654_578_787_389
SQUARE_START = 70_500_002_100_001
SQUARE_END = 100_000_000_000_000


def core_time():
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    return usage.ru_utime+usage.ru_stime


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('binary_directory',type=Path)
    parser.add_argument('output_directory',type=Path)
    parser.add_argument('--cpu',type=int,help='pin a single-worker run to this logical CPU on Linux')
    parser.add_argument('--workers',type=int,default=1,help='run this many concurrent single-threaded jobs')
    parser.add_argument('--rows',type=int,default=1_000_000,help='rows per job, two jobs per worker')
    parser.add_argument('--kind', choices=['direct','square'], required=True)
    args=parser.parse_args()
    low, high = (LOW_START, HIGH_END) if args.kind=='direct' else (SQUARE_START, SQUARE_END)
    if args.rows < 1 or args.workers < 1 or args.rows*args.workers > (high-low+1)//2:
        parser.error('Expected positive, nonoverlapping job sizes')
    if args.cpu is not None and (args.workers != 1 or not hasattr(os,'sched_setaffinity')):
        parser.error('--cpu requires a single Linux worker')
    cpu=None
    if args.workers==1 and hasattr(os,'sched_getaffinity'):
        allowed=os.sched_getaffinity(0)
        cpu=min(allowed) if args.cpu is None else args.cpu
        if cpu not in allowed:
            parser.error('Selected CPU is unavailable')
        os.sched_setaffinity(0,{cpu})
    runner = Path(__file__).with_name('certify_power_shard.sh').resolve()
    def measure(first):
        last=first+args.rows-1
        subprocess.run(['bash',str(runner),str(first),str(last),
                        str(args.output_directory.resolve()),str(args.binary_directory.resolve())],check=True)
        return (args.output_directory/f'{first}-{last}.iw.gz').stat().st_size
    starts=[base+i*args.rows for base in (low,high+1-args.rows*args.workers)
            for i in range(args.workers)]
    begin=time.perf_counter()
    usage=core_time()
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        sizes=list(pool.map(measure,starts))
    elapsed=time.perf_counter()-begin
    cost=core_time()-usage
    rows=args.rows*len(starts)
    print(json.dumps(dict(rows=rows,workers=args.workers,pinned_cpu=cpu,core_seconds=cost,
                          wall_seconds=elapsed,bytes=sum(sizes),whole_machine_bases_per_second=rows/elapsed,
                          kind=args.kind),indent=2))


if __name__=='__main__':
    main()

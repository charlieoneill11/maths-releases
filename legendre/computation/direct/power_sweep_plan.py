"""Exact zero-based job ranges and coverage checks for the remaining 11/5 band."""
import argparse
import re
import subprocess
import sys
from pathlib import Path

FIRST = 3_883_855_444_452
LAST = 32_654_577_787_389
JOB_SIZE = 1_000_000_000
SHARD = re.compile(r'([1-9][0-9]*)-([1-9][0-9]*)\.iw\.gz')
SINGLE = re.compile(r'([1-9][0-9]*)\.pratt\.json')


def job(index):
    start = FIRST + index*JOB_SIZE
    if index < 0 or start > LAST:
        raise ValueError('Job index outside this sweep')
    return start, min(LAST, start+JOB_SIZE-1)


def checked_cover(files, first, last):
    members = []
    for path in files:
        match = SHARD.fullmatch(path.name)
        if match:
            start, end = map(int, match.groups())
        else:
            match = SINGLE.fullmatch(path.name)
            if not match:
                continue
            start = end = int(match[1])
        if end < start:
            raise ValueError(f'Reversed range: {path.name}')
        if end >= first and start <= last:
            members.append((start,end,path))
    members.sort()
    cursor = first
    for start,end,path in members:
        if start != cursor or end > last:
            raise ValueError(f'Expected the next range to begin at {cursor}; found {path.name}')
        cursor = end+1
    if cursor != last+1:
        raise ValueError(f'Witnesses missing from {cursor}')
    return members


def replay(first,last,directory,binaries):
    if not 0 < first <= last:
        raise ValueError('Invalid inclusive replay bounds')
    members = checked_cover(directory.iterdir(),first,last)
    for start,end,path in members:
        if path.name.endswith('.pratt.json'):
            subprocess.run([sys.executable,str(Path(__file__).with_name('power_pratt_fallback.py')),
                            'verify',str(path),'--expected-base',str(start)],check=True)
        else:
            # Passing parameters as separate arguments avoids shell interpretation
            # of paths. pipefail propagates even a late decoder or CRC failure.
            subprocess.run(['bash','-o','pipefail','-c',
                            'gzip -dc -- "$1" | "$2" unpack | "$3" "$4" "$5"',
                            'replay',str(path),str((binaries/'interval_witness_codec').resolve()),
                            str((binaries/'check_power_witnesses').resolve()),str(start),str(end)],
                           check=True)
    print(f'Verified the entire inclusive range {first} through {last}.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='action',required=True)
    plan = commands.add_parser('plan')
    plan.add_argument('index',nargs='?',type=int,help='print only this job, zero-based')
    check = commands.add_parser('replay')
    check.add_argument('first',type=int)
    check.add_argument('last',type=int)
    check.add_argument('directory',type=Path)
    check.add_argument('binaries',type=Path)
    args = parser.parse_args()
    if args.action == 'replay':
        replay(args.first,args.last,args.directory,args.binaries)
    elif args.index is not None:
        print(*job(args.index))
    else:
        for index in range((LAST-FIRST)//JOB_SIZE+1):
            print(index,*job(index),sep='\t')


if __name__ == '__main__':
    main()

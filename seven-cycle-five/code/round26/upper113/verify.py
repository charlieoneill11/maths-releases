"""Regenerate the complete adjacent full-band search from the 33-set atlas."""
import csv
import hashlib
import os
from collections import Counter
from itertools import combinations, combinations_with_replacement
from pathlib import Path
import subprocess
import tempfile

from exterior import exact_extensions

HERE = Path(__file__).resolve().parent
ATLAS = HERE.parent.parent / 'round25' / 'multiplicities' / 'atlas' / 'atlas.tsv'


def check_profiles():
    best = Counter()
    for missing in combinations_with_replacement(range(7),5):
        deficits = [missing.count(i) for i in range(7)]
        levels = [14+sum(deficits[(i+k)%7] for k in (1,3,5)) for i in range(7)]
        if sum(levels)!=113 or any(levels[i]+levels[(i+1)%7]!=33-deficits[i] for i in range(7)):
            raise ValueError('incorrect 113-word profile')
        centers = [i for i in range(7) if not deficits[i] and not deficits[i-1]]
        if centers:
            best[max(levels[i] for i in centers)] += 1
    if best!={16:14,17:147,18:154,19:105}:
        raise ValueError('incorrect census of eligible shared levels')
    print('Best shared levels among the 420 adjacent profiles', dict(sorted(best.items())))


def check_example():
    example = [tuple(map(int,line.split())) for line in (HERE/'example-105.txt').read_text().splitlines()]
    if len(example)!=105 or len(set(example))!=105:
        raise ValueError('incorrect example size')
    if any(len(p)!=4 or any(x not in range(7) for x in p) for p in example):
        raise ValueError('invalid example coordinate')
    if any(all((a-b)%7 in (0,1,6) for a,b in zip(p,q)) for p,q in combinations(example,2)):
        raise ValueError('conflict in the 105-word example')
    for a in range(4):
        if (sum(p[a]==0 for p in example)!=19 or
            any(sum((p[a]-s)%7<2 for p in example)!=33 for s in (6,0))):
            raise ValueError('incorrect marked levels in example')
    print('Checked the 105-word witness with four 19-word centers and eight full bands.')


def main():
    check_profiles()
    check_example()
    if hashlib.sha256(ATLAS.read_bytes()).hexdigest() != 'aee14d35c2f1ef09e27a1e65852d96499ad902fe6cfcda436fcc91078172e38a':
        raise ValueError('unrecognized 33-set atlas')
    with (HERE/'census.tsv').open() as f:
        census = [[int(v) for v in row.values()] for row in csv.DictReader(f,delimiter='\t')]
    if [r[0] for r in census]!=list(range(16,34)):
        raise ValueError('incomplete overlap census')
    with tempfile.TemporaryDirectory() as folder:
        work = Path(folder)
        def run(name, *args):
            print('Running',name,flush=True)
            binary = work/name
            subprocess.run([os.environ.get('CXX','c++'),'-std=c++17','-O3','-march=native',
                            str(HERE/f'{name}.cpp'),'-o',binary],check=True)
            return subprocess.run([binary,ATLAS,*map(str,args)],cwd=work,check=True,
                                  stdout=subprocess.PIPE,text=True).stdout.splitlines()
        pair_counts = [list(map(int,line.split())) for line in run('pair_supports',33,'pairs.bin')]
        if ([r[0] for r in pair_counts]!=list(range(1016)) or
            sum(r[1] for r in pair_counts)!=16672544 or
            any(len(r)!=20 for r in pair_counts) or
            [sum(r[i] for r in pair_counts) for i in range(2,20)] != [r[1] for r in census]):
            raise ValueError('support pair coverage mismatch')
        cuts = run('filter_contacts','pairs.bin','contacts.bin')
        middles = run('middle_layers','contacts.bin','middles.bin')
        joins = run('join_bands','middles.bin','surviving.bin',16,33)
        for lines,expected in ((cuts,[r[:3] for r in census]),
                               (middles,[[r[0],*r[2:6]] for r in census]),
                               (joins,[[r[0],r[5],r[6]] for r in census])):
            counts = [list(map(int,line.split())) for line in lines if line[:1].isdigit()]
            if lines is joins:
                counts = [[k,n,kept] for k,n,computations,kept in counts]
            if counts!=expected:
                raise ValueError('census differs from regeneration')
        pinned = run('check_pinned','middles.bin')
        for line in pinned:
            print(line)
        # Stage 4 redone from coordinates for the two overlap-16 candidates of Stage 3.
        domains = sorted(tuple(map(int,line.split()[2:])) for line in pinned
                         if line.startswith('Pinned domains '))
        obstructions = [line for line in pinned
                        if line.startswith('Transverse pair with no common crossing ')]
        if (len(pinned)!=4 or len(obstructions)!=2 or
                domains!=sorted([(20,33,26,18,9,3),(3,9,18,26,33,20)])):
            raise ValueError(f'pinned overlap-16 check differs: {pinned}')
        if (work/'surviving.bin').stat().st_size != sum(r[6] for r in census)*48:
            raise ValueError('incorrect number of surviving slabs')
        slabs=run('join_slabs','surviving.bin','unions.tsv')
        if slabs!=['Slabs 2852 136896 136896 136896',
                   'After overlap checks 2004 1655 1809 2570',
                   'Independent four-slab unions 1776']:
            raise ValueError(f'slab counts differ: {slabs}')
        print(*slabs,sep='\n')
        exact_extensions(work/'unions.tsv')


if __name__=='__main__':
    main()

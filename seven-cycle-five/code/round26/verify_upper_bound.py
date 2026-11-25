"""Rebuild the three-dimensional atlas and exclude every four-dimensional 113 profile."""
import argparse
import csv
import hashlib
from itertools import combinations_with_replacement
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ATLAS = HERE.parent / 'round25' / 'multiplicities' / 'atlas'
ADJACENT = HERE / 'upper113'
GAP_TWO = HERE / 'nonadjacent113'
ATLAS_SHA256 = 'aee14d35c2f1ef09e27a1e65852d96499ad902fe6cfcda436fcc91078172e38a'
PARTS = ('atlas', 'four-adjacent', 'mixed-adjacent', 'gap-two', 'mixed-gap-two', 'gap-three')


def partition():
    all_profiles = {''.join(p) for p in combinations_with_replacement('123', 4)}
    groups = {
        'four-adjacent': {'1111'},
        'mixed-adjacent': {p for p in all_profiles if p.startswith('1') and p != '1111'},
        'gap-two': {'2222'},
        'mixed-gap-two': {p for p in all_profiles if p.startswith('2') and p != '2222'},
        'gap-three': {'3333'},
    }
    if len(all_profiles) != 15 or set.union(*groups.values()) != all_profiles or sum(map(len, groups.values())) != 15:
        raise ValueError('incomplete or overlapping distance partition')
    with (ADJACENT / 'mixed-census.tsv').open() as f:
        recorded = {r['profile'] for r in csv.DictReader(f, delimiter='\t')}
    if recorded != groups['mixed-adjacent']:
        raise ValueError('a mixed adjacent proof is missing')
    with (GAP_TWO / 'mixed-profiles.tsv').open() as f:
        recorded = {r['ordered_case'] for r in csv.DictReader(f, delimiter='\t')}
    if recorded != groups['mixed-gap-two']:
        raise ValueError('a mixed nonadjacent proof is missing')
    return groups


def native(source, args, tmp, output=None):
    binary = tmp / source.stem
    subprocess.run([os.environ.get('CXX', 'c++'), '-std=c++17', '-O3', source, '-o', binary], check=True)
    subprocess.run([binary, *args], cwd=tmp, stdout=output, check=True)


def python(script, *args):
    subprocess.run([sys.executable, '-B', script, *args], cwd=script.parent, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--part', choices=PARTS, help='replay only one part of the proof')
    args = parser.parse_args()
    if sys.version_info < (3, 10):
        parser.error('Python 3.10 or later is required (upper113/exterior.py uses int.bit_count)')
    # The native and Python replay programs use assertions as proof checks.
    if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
        parser.error('run with Python assertions enabled')
    groups = partition()
    selected = (args.part,) if args.part else PARTS
    atlas = ATLAS / 'atlas.tsv'
    # Every part reads this list of representatives; refuse any other file.
    if hashlib.sha256(atlas.read_bytes()).hexdigest() != ATLAS_SHA256:
        raise ValueError('unrecognized 33-set atlas')
    with tempfile.TemporaryDirectory() as directory:
        tmp = Path(directory)
        for part in selected:
            print('Checking', part, *sorted(groups.get(part, ())), flush=True)
            if part == 'atlas':
                generated = tmp / 'regenerated.tsv'
                with generated.open('wb') as out:
                    native(ATLAS / 'atlas.cpp', [], tmp, out)
                if generated.read_bytes() != atlas.read_bytes():
                    raise ValueError('regenerated atlas differs from the input to the joins')
            elif part == 'four-adjacent':
                python(ADJACENT / 'verify.py')
            elif part == 'mixed-adjacent':
                python(ADJACENT / 'verify_mixed.py', '--profiles', *sorted(groups[part]))
            elif part in ('gap-two', 'mixed-gap-two'):
                python(GAP_TWO / 'verify.py', '--mode', '2222' if part == 'gap-two' else 'mixed')
            else:
                native(ADJACENT / 'gap_three.cpp', [atlas], tmp)
    if args.part:
        print('Completed', args.part)
    else:
        print('All 15 distance profiles exclude size 113. Four-dimensional upper bound 112.')
        print('Twice the five-dimensional size is at most 7 times 112. Upper bound 392.')


if __name__ == '__main__':
    main()

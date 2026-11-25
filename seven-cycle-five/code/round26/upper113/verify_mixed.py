"""Replay distance profiles with a distinguished adjacent pair of full bands."""
import argparse
from collections import Counter
import csv
import hashlib
import os
from itertools import combinations_with_replacement, permutations
from pathlib import Path
import re
import subprocess
import tempfile

from verify import ATLAS, HERE, check_profiles

PROFILES = ['1' + ''.join(gaps) for gaps in combinations_with_replacement('123', 3)
            if gaps != ('1', '1', '1')]
# Unions of adjacent slabs after Stage 5 (the last column of the table in the paper).
STAGE5_UNIONS = {'1112': 0, '1113': 0, '1122': 4, '1123': 64, '1133': 0,
                 '1222': 0, '1223': 0, '1233': 0, '1333': 0}


def distance_orders(gaps):
    """Codes of all distinct orders of the transverse distances, as in atlas.hpp."""
    return {9 * (int(a) - 1) + 3 * (int(b) - 1) + (int(c) - 1) for a, b, c in set(permutations(gaps))}


def expected_counts():
    counts = {}
    with (HERE / 'mixed-census.tsv').open() as f:
        for row in csv.DictReader(f, delimiter='\t'):
            profile = row.pop('profile')
            counts.setdefault(profile, []).append(tuple(map(int, row.values())))
    if set(counts) != set(PROFILES) or set(STAGE5_UNIONS) != set(PROFILES):
        raise ValueError('incomplete mixed distance partition')
    for profile, rows in counts.items():
        if [row[0] for row in rows] != list(range(16, 34)):
            raise ValueError(f'incomplete intersection census for {profile}')
    return counts


def table(output):
    return [tuple(map(int, line.split())) for line in output.splitlines()
            if line and line[0].isdigit()]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profiles', choices=PROFILES, nargs='+',
                        help='profiles to verify, defaulting to all nine mixed exclusions')
    args = parser.parse_args()
    expected = expected_counts()
    requested = args.profiles or sorted(expected)
    check_profiles()
    if hashlib.sha256(ATLAS.read_bytes()).hexdigest() != 'aee14d35c2f1ef09e27a1e65852d96499ad902fe6cfcda436fcc91078172e38a':
        raise ValueError('unrecognized 33-set atlas')
    names = ['pair_supports', 'filter_contacts', 'middle_layers', 'join_bands', 'join_slabs', 'join_remaining']
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        for name in names:
            subprocess.run([os.environ.get('CXX', 'c++'), '-std=c++17', '-O3', '-march=native',
                            str(HERE / f'{name}.cpp'), '-o', root / name], check=True)

        def run(name, *arguments):
            print(f'Running {name}', flush=True)
            return subprocess.run([root / name, ATLAS, *map(str, arguments)], cwd=root,
                                  stdout=subprocess.PIPE, text=True, check=True).stdout

        pairs = root / 'pairs.bin'
        raw = table(run('pair_supports', 33, pairs))
        if (len(raw) != 1016 or [row[0] for row in raw] != list(range(1016)) or
                sum(row[1] for row in raw) != 16672544 or
                pairs.stat().st_size != 8 * 21103868):
            raise ValueError('incomplete normalized support-pair domain')
        for profile in requested:
            print(f'Distance profile {profile}', flush=True)
            with tempfile.TemporaryDirectory(dir=root) as folder:
                path = Path(folder)
                contacts, middles, matches = [path / f'{label}.bin' for label in
                                               ('contacts', 'middles', 'matches')]
                cuts = table(run('filter_contacts', pairs, contacts, profile[1:]))
                # Byte 11 of each 12-byte contact record is its transverse distance code.
                orders = Counter(contacts.read_bytes()[11::12])
                if set(orders) != distance_orders(profile[1:]):
                    raise ValueError(f'missing or unexpected transverse orders in {profile}')
                print(f'{profile}: contact records for all {len(orders)} orders of the transverse distances',
                      flush=True)
                middle = table(run('middle_layers', contacts, middles))
                joined = table(run('join_bands', middles, matches, 16, 33))
                if not (len(cuts) == len(middle) == len(joined) == 18):
                    raise ValueError(f'missing overlap strata in {profile}')
                observed = []
                for k, (c, m, j) in enumerate(zip(cuts, middle, joined), start=16):
                    if (c[0] != k or m[0] != k or j[0] != k or c[2] != m[1] or
                            m[4] != j[1] or c[1] != sum(row[k-14] for row in raw)):
                        raise ValueError(f'inconsistent stage totals at {profile}, overlap {k}')
                    observed.append((k, c[1], c[2], m[2], m[3], m[4], j[2], j[3]))
                if observed != expected[profile]:
                    raise ValueError(f'census differs for {profile}')
                surviving = sum(row[-1] for row in observed)
                if matches.stat().st_size != 48 * surviving:
                    raise ValueError('invalid number of emitted matching slabs')
                if not surviving:
                    if STAGE5_UNIONS[profile] != 0:
                        raise ValueError(f'Stage 5 count differs for {profile}')
                    print(f'{profile} excluded by the six-band join.')
                    continue
                unions = path / 'unions.tsv'
                slabs = run('join_slabs', matches, unions, profile)
                print(slabs, end='')
                found = re.fullmatch(r'Independent ([23])-slab unions (\d+)', slabs.splitlines()[-1])
                if (not found or int(found[1]) != profile.count('1') or
                        int(found[2]) != STAGE5_UNIONS[profile] or
                        len(unions.read_text().splitlines()) != STAGE5_UNIONS[profile]):
                    raise ValueError(f'Stage 5 count differs for {profile}')
                if unions.stat().st_size == 0:
                    print(f'{profile} excluded by the physical slab join.')
                else:
                    remaining = path / 'remaining.tsv'
                    details = run('join_remaining', unions, profile, remaining)
                    print(details.splitlines()[-1])
                    if details.splitlines()[-1] != (f'Nonadjacent projections retain 0 of '
                                                    f'{STAGE5_UNIONS[profile]} slab unions'):
                        raise ValueError(f'Stage 6 output differs for {profile}')
                    if remaining.stat().st_size == 0:
                        print(f'{profile} excluded by the remaining full-band projections.')
                    else:
                        raise ValueError(f'physical unions remain for recorded exclusion {profile}')


if __name__ == '__main__':
    main()

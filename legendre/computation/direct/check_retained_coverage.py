"""Reconcile retained power and square certificates after the historical sweep plans.

Run replay.sh first to verify the primality of the binary archives. This program
also verifies every additional alternative witness it uses for square credit.
"""
import argparse
import csv
from math import isqrt
from pathlib import Path
from subprocess import PIPE, Popen

from check_square_power_nesting import FIRST, LAST, PREFIX, TARGET, root_floor
from power_pilot_certificates import prove

HERE = Path(__file__).resolve().parent
PILOT_STARTS = (
    ('midpoint85', 85_249_999_000_001),
    ('target100', 99_999_999_000_001),
)


def decoded(path, codec):
    with Popen(['gzip', '-dc', '--', str(path)], stdout=PIPE) as unzip:
        with Popen([str(codec.resolve()), 'unpack'], stdin=unzip.stdout, stdout=PIPE) as decoder:
            unzip.stdout.close()
            for line in decoder.stdout:
                n, p = line.split()
                yield int(n), int(p)
            if decoder.wait():
                raise ValueError(f'Decoding failed for {path}')
        if unzip.wait():
            raise ValueError(f'Decompression failed for {path}')


def complement(first, last, covered):
    cursor = first
    for lo, hi in sorted(covered):
        if cursor > last:
            break
        if hi < cursor or lo > last:
            continue
        if cursor < lo:
            yield cursor, lo - 1
        cursor = max(cursor, hi + 1)
    if cursor <= last:
        yield cursor, last


def square_to_power(codec):
    # Consecutive selected square witnesses have square roots less than two
    # apart, while every complete power interval in sqrt coordinates is wider.
    assert 11**10 * FIRST > 20**10
    power_ranges = []
    for name, first in PILOT_STARTS:
        path = HERE.parent / 'squares' / f'{name}.iw.gz'
        for j, (m, p) in enumerate(decoded(path, codec)):
            assert m == first + j and m*m < p < (m+1)**2
            if not j:
                first_p = p
        assert j + 1 == 1_000_000
        lo, hi = (root_floor(q**5, 11) for q in (first_p, p))
        assert FIRST <= lo <= hi <= LAST
        assert lo**11 < first_p**5 < (lo+1)**11 and hi**11 < p**5 < (hi+1)**11
        power_ranges.append((lo, hi))
    assert power_ranges == [(4_616_019_348_273,4_616_019_397_498),
                            (5_336_699_182_690,5_336_699_231_206)]
    return power_ranges


def square_credits(codec, shards, on_credit=None):
    credits = set()
    with (HERE / 'alternative-square-credits.tsv').open() as stream:
        for row in csv.DictReader(stream, delimiter='\t'):
            n,p,m = (int(row[key]) for key in ('n','p','m'))
            prove(n, n**11, (n+1)**11, p)
            assert PREFIX < m <= TARGET and m*m < p < (m+1)**2 and m not in credits
            assert all(not first <= m < first + 1_000_000 for _, first in PILOT_STARTS)
            credits.add(m)
    canonical = 0
    previous_square = 0
    for lo, hi, path in shards:
        # If no square in the target band can intersect this power shard, skip it.
        if lo**11 >= (TARGET+1)**10 or (hi+1)**11 <= (PREFIX+1)**10:
            continue
        for _, p in decoded(path, codec):
            m = isqrt(p)
            if PREFIX < m <= TARGET and m != previous_square:
                assert m*m < p < (m+1)**2
                assert previous_square < m and m not in credits
                assert all(not first <= m < first + 1_000_000 for _, first in PILOT_STARTS)
                canonical += 1
                if on_credit is not None:
                    on_credit(m)
                previous_square = m
    assert canonical == 11_894_829 and len(credits) == 105
    return canonical, len(credits)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--square-codec', type=Path, required=True)
    parser.add_argument('--power-codec', type=Path, required=True)
    args = parser.parse_args()
    shards = []
    for folder in ('sealed', 'continuation'):
        for path in (HERE / folder).glob('*.iw.gz'):
            lo, hi = map(int, path.name.split('.')[0].split('-'))
            shards.append((lo, hi, path))
    shards.sort()
    retained = [(lo, hi) for lo, hi, _ in shards]
    assert all(a[1] < b[0] for a, b in zip(retained, retained[1:]))
    assert sum(hi-lo+1 for lo,hi in retained) == 15_018_635
    square_powers = square_to_power(args.square_codec)
    remaining = list(complement(FIRST, LAST, retained + square_powers))
    count = sum(hi-lo+1 for lo,hi in remaining)
    assert len(remaining) == 8 and remaining[0][0] == 3_883_865_444_452
    assert count == 28_770_711_230_657
    print('Remaining direct bases after all retained credits:')
    for lo,hi in remaining:
        print(f'  {lo:,}..{hi:,}')
    # The longer schedule also reaches the upper continuation and an isolated
    # Pratt certificate beyond the sharp cutoff. replay.sh verifies each file.
    singletons = []
    for path in (HERE / 'examples').glob('pratt-fallback-*.json'):
        n = int(path.stem.rsplit('-', 1)[1])
        singletons.append((n, n))
    bridge_last = 35_000_000_000_000 - 1
    bridge_gaps = list(complement(FIRST, bridge_last, retained + square_powers + singletons))
    bridge_count = sum(hi-lo+1 for lo,hi in bridge_gaps)
    assert len(bridge_gaps) == 10 and bridge_count == 31_116_131_443_266
    print(f'Direct outstanding for the 35-trillion cutoff: {bridge_count:,} bases.')
    canonical, extra = square_credits(args.power_codec, shards)
    square_count = TARGET - PREFIX - canonical - 2_000_000 - extra
    overlap_end = root_floor(TARGET**10, 11)
    direct_hybrid = sum(hi-lo+1 for lo,hi in complement(overlap_end+1, LAST, retained))
    assert direct_hybrid == 27_317_877_541_645
    print(f'Direct outstanding: {count:,}; additional distinct square bases: {extra:,}')
    print(f'Historical hybrid outstanding: {square_count:,} square + {direct_hybrid:,} power = '
          f'{square_count+direct_hybrid:,} bases.')
    combined = [(max(lo, overlap_end + 1), hi) for lo, hi in bridge_gaps if hi > overlap_end]
    fast_last = 32_700_000_000_000
    for label, ranges in (('Power alone', bridge_gaps), ('Combined power', combined)):
        fast = sum(min(hi, fast_last) - lo + 1 for lo, hi in ranges if lo <= fast_last)
        upper = sum(hi - max(lo, fast_last + 1) + 1 for lo, hi in ranges if hi > fast_last)
        print(f'{label}: {fast:,} fast + {upper:,} GMP = {fast+upper:,}')
    combined_power = sum(hi - lo + 1 for lo, hi in combined)
    assert (square_count, combined_power) == (29_499_984_005_066, 29_663_297_754_254)
    print(f'35T combined: {square_count:,} square + {combined_power:,} power = '
          f'{square_count+combined_power:,} bases.')


if __name__ == '__main__':
    main()

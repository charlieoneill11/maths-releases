"""Exact interval and archive-reuse counts for a square/11th-fifth hybrid sweep."""
import argparse
from fractions import Fraction
from math import isqrt
from pathlib import Path
from subprocess import PIPE, Popen

from power_sweep_plan import FIRST, LAST

PUBLISHED = 70_500_000_000_000
PREFIX = PUBLISHED + 2_100_000
TARGET = 10**14
PILOT_ENDS = (85_250_000_000_000, TARGET)
PILOT_SIZE = 1_000_000
SHARDS = (
    (3_883_853_444_451, 3_883_854_444_451, 894_829),
    (3_883_854_444_452, FIRST-1, 1_000_000),
    (LAST+1, 32_654_578_787_389, 0),
)


def root_floor(x, degree):
    low, high = 0, 1 << ((x.bit_length()+degree-1)//degree)
    while high-low > 1:
        mid = (low+high)//2
        if mid**degree <= x:
            low = mid
        else:
            high = mid
    assert low**degree <= x < (low+1)**degree
    return low


def square_base_bounds(n):
    x = n**11
    first = root_floor(x,10)
    first += first**10 < x
    last = root_floor((n+1)**11,10)-1
    return first,last


def archive_credit(directory, codec):
    previous_square = -1
    total = 0
    for lo,hi,expected_credit in SHARDS:
        path = directory/f'{lo}-{hi}.iw.gz'
        with Popen(['gzip','-dc','--',str(path)],stdout=PIPE) as unzip:
            with Popen([str(codec.resolve()), 'unpack'], stdin=unzip.stdout, stdout=PIPE) as decoder:
                unzip.stdout.close()
                expected = lo
                credit = 0
                for line in decoder.stdout:
                    n,p = map(int,line.split())
                    m = isqrt(p)
                    if n != expected or not previous_square < m or not m*m < p < (m+1)**2:
                        raise ValueError(f'Invalid row or duplicate square at {n}')
                    expected += 1
                    previous_square = m
                    credit += PREFIX < m <= TARGET
                if decoder.wait() or expected != hi+1 or credit != expected_credit:
                    raise ValueError(f'Archive credit failed for {path}')
            if unzip.wait():
                raise ValueError(f'Decompression failed for {path}')
        total += credit
    return total


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--shards', type=Path, help='Replay the square-index overlap from the three already certified primary archives')
    parser.add_argument('--codec', type=Path, default=Path('interval_witness_codec'))
    args = parser.parse_args()
    lo,hi = square_base_bounds(FIRST)[1],square_base_bounds(LAST)[0]
    direct = LAST-FIRST+1
    count = hi-lo+1
    assert (lo,hi,count) == (70_500_039_934_612,733_395_904_053_766,662_895_864_119_155)
    # Convexity and the lower-end derivative ensure every cell has a complete square.
    assert 11**10*FIRST > 20**10  # (11/10) FIRST^(1/10) > 2
    last_nested = root_floor(TARGET**10,11)
    assert last_nested == 5_336_699_231_206
    assert square_base_bounds(last_nested)[0] <= TARGET
    assert (last_nested+1)**11 > (TARGET+1)**10
    reuse = sum(row[2] for row in SHARDS)
    if args.shards is not None:
        assert archive_credit(args.shards,args.codec) == reuse
    pilot_powers = 0
    for last_square in PILOT_ENDS:
        first_square = last_square-PILOT_SIZE+1
        # The already retained power shards are either wholly below or wholly above these square blocks.
        for first,last,_ in SHARDS:
            assert (last+1)**11 < first_square**10 or first**11 > (last_square+1)**10
        induced = root_floor((first_square+1)**10,11)
        induced += induced**11 < (first_square+1)**10
        left,right = induced-1,root_floor(last_square**10,11)
        assert FIRST <= left <= right <= LAST
        pilot_powers += right-left+1
    assert pilot_powers == 97_742
    new_squares = TARGET-PREFIX-reuse-PILOT_SIZE*len(PILOT_ENDS)
    new_powers = LAST-last_nested
    hybrid = new_squares+new_powers
    assert (new_squares,new_powers,hybrid) == (29_499_994_005_171,27_317_878_556_183,56_817_872_561_354)
    print(f'Shortest contiguous square sweep: {lo:,}..{hi:,} ({count:,}, {float(Fraction(count,direct)):.8f} times the direct count).')
    print(f'Hybrid to {TARGET:,}: {new_squares:,} new squares after {reuse:,} primary credits and two separate million-square pilots, and {new_powers:,} new powers.')
    print(f'Square pilot blocks certify {pilot_powers:,} primary bases by nesting inside the contiguous power plan.')
    print(f'Combined {hybrid:,} compared with {direct:,} direct witnesses ({float(Fraction(hybrid,direct)):.8f} times).')


if __name__ == '__main__':
    main()

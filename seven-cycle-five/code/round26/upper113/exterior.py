"""Compute exact extension sizes for the independent, matched physical slabs."""
from collections import Counter
from functools import lru_cache
from itertools import product
from pathlib import Path
import sys


def bit_indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit


def exact_extensions(path):
    words = list(product(range(7), repeat=4))
    index = {p:i for i,p in enumerate(words)}
    # All the points in a selected slab are fixed. Every additional word
    # must have all four coordinates outside the three marked levels.
    exterior = [i for i,p in enumerate(words) if all(2 <= u <= 5 for u in p)]
    conflicts = []
    for p in words:
        near = (tuple((u+k) % 7 for u,k in zip(p,delta))
                for delta in product((-1,0,1), repeat=4) if any(delta))
        conflicts.append(sum(1 << index[q] for q in near))
    exterior_bits = sum(1 << i for i in exterior)
    marked_bands = [[sum(1 << i for i,p in enumerate(words) if (p[a]-start)%7 < 2)
                     for start in (6,0)] for a in range(4)]

    @lru_cache(maxsize=None)
    def maximum(available):
        """Partition all independent extensions by whether they use one pivot."""
        if not available:
            return 0
        pivot = max(bit_indices(available), key=lambda i:(available & conflicts[i]).bit_count())
        if not available & conflicts[pivot]:
            return available
        bit = 1 << pivot
        rest = available ^ bit
        use = bit | maximum(rest & ~conflicts[pivot])
        skip = maximum(rest)
        return use if use.bit_count() >= skip.bit_count() else skip

    inside_histogram, total_histogram = Counter(), Counter()
    seen = set()
    for line in Path(path).read_text().splitlines():
        row = tuple(map(int,line.split()))
        if not row or any(not 0 <= i < 2401 for i in row) or sorted(set(row)) != list(row):
            raise ValueError('invalid slab union')
        inside = sum(1 << i for i in row)
        if inside in seen or inside & exterior_bits:
            raise ValueError('duplicate union or point outside the slabs')
        seen.add(inside)
        for left,right in marked_bands:
            if (inside & left).bit_count() != 33 or (inside & right).bit_count() != 33:
                raise ValueError('incomplete marked band')
            if not 16 <= (inside & left & right).bit_count() <= 19:
                raise ValueError('incorrect marked center size')
        forbidden = 0
        for i in row:
            forbidden |= conflicts[i]
        if inside & forbidden:
            raise ValueError('slab union is not independent')
        addition = maximum(exterior_bits & ~forbidden)
        full = inside | addition
        if any(full & conflicts[i] for i in bit_indices(addition)):
            raise ValueError('invalid exterior optimum')
        inside_histogram[len(row)] += 1
        total_histogram[full.bit_count()] += 1
    if inside_histogram != {97:720,98:736,99:280,100:40}:
        raise ValueError(f'unexpected slab sizes {inside_histogram}')
    if total_histogram != {101:24,102:80,103:1328,104:320,105:24}:
        raise ValueError(f'unexpected completion maxima {total_histogram}')
    print('Independent slab unions by size', dict(sorted(inside_histogram.items())))
    print('Exact maxima after exterior completion', dict(sorted(total_histogram.items())))


if __name__ == '__main__':
    exact_extensions(sys.argv[1])

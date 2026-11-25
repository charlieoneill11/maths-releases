"""Check the transfer of the 33-band certificates to level profiles at size 112."""
from collections import Counter
from itertools import combinations_with_replacement
from math import comb


def orbit_key(deficits):
    return min(seq[i:] + seq[:i] for seq in (deficits, deficits[::-1]) for i in range(7))


def classify(d):
    levels = [13 + sum(d[(i + j) % 7] for j in (1, 3, 5)) for i in range(7)]
    if sum(levels) != 112 or any(levels[i] + levels[(i + 1) % 7] != 33 - d[i]
                                 for i in range(7)):
        raise ValueError('invalid inversion of the seven band sizes')
    full = {i for i in range(7) if d[i] == 0}
    if len(full) < 2:
        return 'zero or one full band'
    if any((i - 1) % 7 in full and 16 <= levels[i] <= 19 for i in full):
        return 'adjacent source'
    gap_two = [i for i in full if (i + 2) % 7 in full]
    gap_three = any((i + 3) % 7 in full for i in full)
    if not gap_two and not gap_three:
        raise ValueError('axis with two full bands has no usable pair')
    if any(d[(i + 1) % 7] <= 2 and all(14 <= levels[(i + j) % 7] <= 19 for j in (1, 2))
           for i in gap_two):
        return 'distance-two source'
    if gap_three:
        return 'distance-three pair'
    if orbit_key(d) != orbit_key((0, 3, 0, 1, 1, 1, 1)):
        raise ValueError('unexpected remaining pair class')
    return 'size-30 bridge'


def main():
    labelled = Counter()
    orbits = {}
    for missing in combinations_with_replacement(range(7), 7):
        d = tuple(missing.count(i) for i in range(7))
        group = classify(d)
        labelled[group] += 1
        previous = orbits.setdefault(orbit_key(d), group)
        if group != previous:
            raise ValueError('classification depends on the representative')
    counts = Counter(orbits.values())
    groups = ('zero or one full band', 'adjacent source', 'distance-two source',
              'distance-three pair', 'size-30 bridge')
    if ([counts[x] for x in groups] != [4, 86, 23, 19, 1] or
            [labelled[x] for x in groups] != [43, 1141, 301, 224, 7]):
        raise ValueError('unexpected axis profile census')
    for group in groups:
        print(f'{group}: {counts[group]} classes, {labelled[group]} labelled profiles')

    # The axes may be permuted. In the residual multisets, remove one copy
    # of the required exceptional class and choose the other three freely.
    rich = sum(counts[g] for g in groups[1:])
    exceptional_family = counts['distance-three pair'] + counts['size-30 bridge']
    residual = comb(exceptional_family + 2, 3)
    excluded = comb(rich + 3, 4) - residual
    total = comb(len(orbits) + 3, 4)
    if (rich, residual, excluded, total) != (129, 1540, 12081245, 13633830):
        raise ValueError('unexpected four-axis multiset census')
    print(f'Excluded {excluded:,} of {comb(rich + 3, 4):,} four-axis multisets with two full bands per axis.')
    print(f'The transferred 113 certificates leave {residual:,} of those multisets and {total-excluded:,} in total.')
    print(f'After the separate physical bridge proof, {total - excluded - residual:,} multisets with a sparse axis remain.')


if __name__ == '__main__':
    main()

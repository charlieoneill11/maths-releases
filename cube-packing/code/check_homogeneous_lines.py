"""Independently check the full-line implication for the 261 and 301 catalogues.

Usage: python3 check_homogeneous_lines.py SIDE planes.bin
The input is the sorted catalogue emitted by enumerate_85.py --homogeneous.
"""
import sys
from struct import iter_unpack


class Checker:
    def __init__(self, side):
        self.side = side
        self.m = (side - 1) // 4
        self.mask = (1 << side) - 1
        self.axes = ((1, 2), (0, 2), (0, 1))
        self.slopes = [
            sign * 2 * d
            for d in range(1, self.m + 1) if self.m % d == 0
            for sign in (1, -1)
        ]
        self.intervals = [sum(1 << ((h + i) % side)
                              for i in range(2, side, 2)) for h in range(side)]
        self.holes_at_point = [
            sum(1 << h for h, row in enumerate(self.intervals) if (row >> i) & 1)
            for i in range(side)
        ]

    def successor(self, bits):
        return ((bits << 1) & self.mask) | (bits >> (self.side - 1))

    def predecessor(self, bits):
        return (bits >> 1) | ((bits & 1) << (self.side - 1))

    def project(self, slope, phase):
        # Each selected value of v - slope*u lies in one block of the
        # maximum pattern. Its translates cover every nonhole square once.
        d = abs(slope) // 2
        values = {2*i + 4*d*j for i in range(d) for j in range(self.m // d)}
        shift = phase + 2 + max(0, -slope)
        return [
            sum(1 << ((value + shift + slope*u) % self.side) for value in values)
            for u in range(self.side)
        ]

    def decode(self, entry):
        n = self.side
        planes = []
        for axis in range(3):
            pair = []
            for index in range(2):
                slope, phase = entry[3+4*axis+2*index:5+4*axis+2*index]
                if slope > n // 2:
                    slope -= n
                points = self.project(slope, phase)
                pair.append((index * entry[axis], slope, phase,
                             [points, self.transpose(points)]))
            planes.append(pair)
        return planes

    def transpose(self, rows):
        columns = [0] * self.side
        for i, row in enumerate(rows):
            for j in indices(row):
                columns[j] |= 1 << i
        return columns

    def hole(self, plane, axis, coordinate_axis, t):
        _, slope, phase, _ = plane
        if coordinate_axis == self.axes[axis][0]:
            return (slope*t + phase) % self.side
        return ((t-phase) * pow(slope, -1, self.side)) % self.side

    def shared_bounds(self, planes):
        bounds = []
        n = self.side
        for axis, (u, v) in enumerate(self.axes):
            feasible = 0
            for t in range(n):
                a, b = [(p[0], self.hole(p, u, axis, t)) for p in planes[u]]
                c, d = [(self.hole(p, v, axis, t), p[0]) for p in planes[v]]
                feasible += any(
                    all(((y-a[1]) - s*(x-a[0])) % n == 0 for x, y in (b, c, d))
                    for s in self.slopes
                )
            bounds.append(max(0, self.m + 1 - feasible))
        return bounds

    def full_patterns(self, occupied, empty, holes, covered, shareable, floor):
        candidates = self.mask & ~covered
        if holes:
            if holes & (holes - 1):
                return 0
            candidates &= holes
        for i in indices(occupied):
            candidates &= self.holes_at_point[i]
            if not candidates:
                return 0
        for i in indices(empty):
            candidates &= ~self.holes_at_point[i]
            if not candidates:
                return 0
        return sum(1 << h for h in indices(candidates)
                   if (self.intervals[h] & shareable).bit_count() >= floor)

    def neighbor(self, planes, axis, base, direction, bounds):
        n, mask = self.side, self.mask
        u, v = self.axes[axis]
        height, _, _, base_rows = base
        level, shared = (height+direction) % n, (height+(direction > 0)) % n
        have, lack = [[0]*n for _ in range(2)]
        selected, unselected, hole, covered = (
            [[0]*n for _ in range(2)] for _ in range(4)
        )
        full_inputs = [{p[0] for p in planes[k]} for k in (u, v)]
        for d, transverse in enumerate((u, v)):
            for p in planes[transverse]:
                t = p[0]
                following = (t+1) % n
                h = self.hole(p, transverse, axis, level)
                selected[d][t] = self.intervals[h]
                unselected[d][t] = mask ^ self.intervals[h]
                shared_points = p[3][self.axes[transverse].index(axis)][shared]
                first = shared_points & base_rows[d][t]
                second = shared_points & base_rows[d][following]
                if first | second != shared_points:
                    return False
                if d == 0:
                    have[t] |= first
                    have[following] |= second
                else:
                    for j in indices(first):
                        have[j] |= 1 << t
                    for j in indices(second):
                        have[j] |= 1 << following

        # In each round take the square consequences in the current chart,
        # then the projected line consequences in both coordinate charts.
        while True:
            previous = tuple(map(tuple, [have, lack, *selected, *unselected, *hole, *covered]))
            if any(a & b for a, b in zip(have, lack)):
                return False
            cross_holes = [self.transpose(h) for h in hole]
            cross_covered = [self.transpose(c) for c in covered]
            for x in range(n):
                row = have[x]
                near = row | self.successor(row) | self.predecessor(row)
                lack[(x-1) % n] |= near
                lack[(x+1) % n] |= near
                lack[x] |= self.successor(row) | self.predecessor(row)
                h = hole[0][x] | cross_holes[1][x]
                h |= self.successor(h)
                lack[x] |= h
                lack[(x+1) % n] |= h

            for d, k in enumerate((u, v)):
                on = have if d == 0 else self.transpose(have)
                off = lack if d == 0 else self.transpose(lack)
                newly_on, newly_off = [0]*n, [0]*n
                candidates = []
                for t in range(n):
                    j = (t+1) % n
                    allowed0, allowed1 = mask ^ off[t], mask ^ off[j]
                    occupied = on[t] | on[j]
                    blocked = off[t] & off[j]
                    h = hole[d][t] | cross_holes[1-d][t]
                    c = covered[d][t] | cross_covered[1-d][t]
                    h |= blocked & self.predecessor(blocked)
                    c |= occupied | self.predecessor(occupied)
                    if h & c or (selected[d][t] | occupied) & (unselected[d][t] | blocked):
                        return False
                    # A covered square with a single available corner fixes it.
                    left = (allowed0, self.predecessor(allowed0),
                            allowed1, self.predecessor(allowed1))
                    for index, available in enumerate(left):
                        unique = c & available
                        for other, alternative in enumerate(left):
                            if other != index:
                                unique &= ~alternative
                        row = t if index < 2 else j
                        newly_on[row] |= self.successor(unique) if index % 2 else unique
                    newly_on[t] |= selected[d][t] & off[j]
                    newly_on[j] |= selected[d][t] & off[t]
                    newly_off[t] |= unselected[d][t]
                    newly_off[j] |= unselected[d][t]
                    shareable = (allowed0 & base_rows[d][t]) | (allowed1 & base_rows[d][j])
                    floor = self.m if t in full_inputs[d] else bounds[k]
                    candidates.append(self.full_patterns(
                        selected[d][t] | occupied, unselected[d][t] | blocked,
                        h, c, shareable, floor))
                bad = candidates.count(0)
                if bad > 2:
                    return False
                if bad == 2:
                    for t, choices in enumerate(candidates):
                        if not choices:
                            continue
                        if choices.bit_count() == 1:
                            hole[d][t] |= choices
                        covered[d][t] |= mask ^ choices
                        common = mask
                        ever = 0
                        for h in indices(choices):
                            common &= self.intervals[h]
                            ever |= self.intervals[h]
                        selected[d][t] |= common
                        unselected[d][t] |= mask ^ ever
                if d:
                    newly_on = self.transpose(newly_on)
                    newly_off = self.transpose(newly_off)
                have = [a | b for a, b in zip(have, newly_on)]
                lack = [a | b for a, b in zip(lack, newly_off)]
            if tuple(map(tuple, [have, lack, *selected, *unselected, *hole, *covered])) == previous:
                return True

    def survives(self, planes):
        bounds = self.shared_bounds(planes)
        for axis, (first, second) in enumerate(planes):
            if not any(self.neighbor(planes, axis, first, d, bounds)
                       and self.neighbor(planes, axis, second, -d, bounds)
                       for d in (-1, 1)):
                return False
        return True


def indices(bits):
    while bits:
        low = bits & -bits
        yield low.bit_length() - 1
        bits ^= low


def main(side, filename):
    expected = {261: 114, 301: 38}[side]
    checker = Checker(side)
    with open(filename, 'rb') as source:
        records = list(iter_unpack('>15H', source.read()))
    survivors = [i for i, r in enumerate(records, 1) if checker.survives(checker.decode(r))]
    print(f'{side}: {len(records)} orbits, survivors {survivors}', flush=True)
    return int(len(records) != expected or bool(survivors))


if __name__ == '__main__':
    sys.exit(main(int(sys.argv[1]), sys.argv[2]))

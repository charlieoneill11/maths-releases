"""Exact certificate replay. Run with Python 3. No external dependencies."""

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations


def check_slots(n, q, slots, simple):
    """Verify cyclic separations at each vertex and the odd-order density bound."""
    p = len(slots)
    at = [[] for _ in range(n)]
    multiplicity = Counter()
    for colour, edges in enumerate(slots):
        for u, v in edges:
            assert 0 <= u < n and 0 <= v < n and u != v
            multiplicity[tuple(sorted((u, v)))] += 1
            at[u].append(colour)
            at[v].append(colour)
    for colours in at:
        if colours:
            cyclic = colours[1:] + [colours[0] + p]
            assert all(y - x >= q for x, y in zip(colours, cyclic))
    if simple:
        assert max(multiplicity.values()) == 1
    degree = max(map(len, at))
    density = Fraction(sum(multiplicity.values()), n // 2)
    assert density == Fraction(p, q)
    assert density.denominator == q
    assert degree + Fraction(1, 2) < density < degree + 1
    return degree, density, multiplicity


def check_multicycles():
    for q in range(3, 65):
        n = 2*q + 1
        slots = [[(2*j % n, (2*j + 1) % n)] for j in range(n*(q-1))]
        degree, value, mult = check_slots(n, q, slots, False)
        assert degree == 2*(q-1) and value == degree + 1 - Fraction(1, q)
        assert len(mult) == n and set(mult.values()) == {q-1}
    print("Multicycle certificates passed for 3 <= q <= 64")


def check_circulant(n, q, base):
    p = n * len(base)
    slots = [[] for _ in range(p)]
    for shift in range(n):
        for residue, edges in enumerate(base):
            colour = q * (len(base)*shift + residue) % p
            slots[colour] = [((u+shift) % n, (v+shift) % n) for u, v in edges]
    degree, value, _ = check_slots(n, q, slots, True)
    return degree, value


def check_published():
    # aadrianvv's Theorem 1, Theorem 2 and Section 7.2, cited in the paper.
    for g in range(2, 11):
        a = [(0, 4*g)] + [(2*g+1+i, 4*g-i) for i in range(1, g)]
        b = [(1, 3*g+1)] + [(2*g+1+i, 4*g+1-i) for i in range(1, g)]
        assert check_circulant(6*g+1, 3, [a, b]) == (4*g, 4*g+Fraction(2, 3))
    base4 = [[(0, 1), (2, 9), (10, 24)], [(0, 2), (1, 10), (11, 24)],
             [(0, 3), (1, 11), (2, 10)]]
    base5 = [[(0, 11), (1, 2), (3, 10)], [(0, 3), (1, 11), (2, 10)],
             [(0, 12), (1, 3), (2, 11)]]
    assert check_circulant(25, 4, base4) == (18, Fraction(75, 4))
    assert check_circulant(31, 5, base5) == (18, Fraction(93, 5))
    print("Published simple-graph certificates passed for q = 3, 4, 5")


def cover_fractional_index(n, h, t):
    """Maximize induced edge count at each odd order in a cyclic fibre graph."""
    masks = range(1 << h)
    weights = [mask.bit_count() for mask in masks]
    period_mask = (1 << h) - 1
    links = []
    for left in masks:
        shifts = [((left << j) | (left >> (h-j))) & period_mask for j in range(t)]
        links.append([sum((shift & right).bit_count() for shift in shifts)
                      for right in masks])

    best = Fraction(2*t)
    for first in masks:
        states = {(first, weights[first]): 0}
        for _ in range(1, n):
            new = {}
            for (left, count), edge_count in states.items():
                for right in masks:
                    key = (right, count + weights[right])
                    new[key] = max(new.get(key, -1), edge_count + links[left][right])
            states = new
        for (last, count), edge_count in states.items():
            if count >= 3 and count % 2:
                density = Fraction(2*(edge_count + links[last][first]), count-1)
                best = max(best, density)
    return best


def check_covers():
    for n in (5, 7, 9):
        for t in (2, 3):
            least_odd = t if t % 2 else t+1
            bound = 2*t + Fraction(2*t, n*least_odd-1)
            for h in range(t, 5):
                value = cover_fractional_index(n, h, t)
                assert value <= bound
                if h == least_odd:
                    assert value == bound
    print("Sharp cover bounds passed by exact optimization over odd vertex sets")


def check_classification_examples():
    for q in range(2, 41):
        n = 2*q+1
        complete = [(i % q, q+i % (q+1)) for i in range(q*(q+1))]
        examples = [(complete, q+1)]
        for cycle_size, spacing, step in [(q+1, q+1, q), (q+2, q, q+1)]:
            period = cycle_size*spacing
            sequence = [None]*period
            for j in range(period):
                i, residue = divmod(j, spacing)
                other = (i-1) % cycle_size if residue == 0 else cycle_size+residue-1
                sequence[j*step % period] = (i, other)
            examples.append((sequence, q+2))
        for sequence, delta in examples:
            assert len(set(tuple(sorted(e)) for e in sequence)) == len(sequence)
            times = [[] for _ in range(n)]
            for c, (u, v) in enumerate(sequence):
                assert u != v
                times[u].append(c)
                times[v].append(c)
            assert max(map(len, times)) == delta
            for row in times:
                assert row and min(y-x for x, y in zip(row, row[1:]+[row[0]+len(sequence)])) >= q
    print("Three classified join families passed for 2 <= q <= 40")


def audit_sequences(q):
    """Enumerate all linear continuations of a fixed initial ordered matching.

    The candidate set uses only unused edges and disjointness from the previous
    q-1 edges. Every ordered initial q-matching is equivalent by relabelling.
    At each length, test the cyclic boundary from the definition.
    """
    n = 2*q+1
    edges = [1 << u | 1 << v for u, v in combinations(range(n), 2)]
    seq = [3 << (2*i) for i in range(q)]
    used = set(seq)
    closed = 0

    def visit():
        nonlocal closed
        if len(seq) > q+1:
            if all(not (seq[-i] & seq[j]) for i in range(1, q)
                   for j in range(q-i)):
                degree = [sum(bool(e & (1 << v)) for e in seq) for v in range(n)]
                assert len(seq) <= q*max(degree)+1
                assert (len(seq), max(degree)) in {(n, 2), (q*(q+1), q+1),
                                                    (q*(q+2), q+2), ((q+1)**2, q+2)}
                for v in range(n):
                    same = sum(bool(e & (1 << v)) and
                               degree[(e ^ (1 << v)).bit_length()-1] == degree[v]
                               for e in seq)
                    assert same <= 2
                closed += 1
        occupied = 0
        for e in seq[-(q-1):]:
            occupied |= e
        for e in edges:
            if e not in used and not e & occupied:
                used.add(e)
                seq.append(e)
                visit()
                seq.pop()
                used.remove(e)
    visit()
    assert closed > 0
    print(f"All {closed} closed normalized sequences on {n} vertices passed")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-sequence-q", type=int, default=5)
    args = parser.parse_args()
    check_multicycles()
    check_published()
    check_covers()
    check_classification_examples()
    for window in range(2, args.max_sequence_q + 1):
        audit_sequences(window)

"""Fully rational lower bound for repairs that may erase, add, and keep labels.

Run after verifying the original coloring:
    python check_exchange.py parts_refined.json exchange_cells.json

Each base source square has six unit translations, one into each old color.
The squares repeat under the period lattice and its additional one-row
color permutation. Distinct translation vectors have disjoint image boxes
on this finer torus. A repaired point in any of these squares therefore
charges a distinct old point at unit distance, in its new color. Unless
that charged point changes label it must become blank. Every measurable
piece is charged by an area-preserving translation. Thus any relabel-free
repair has blank area at least that of the certified squares. More
generally, blank area plus area of changed old labels is at least this
much. This argument applies to every finite superperiod with its natural
area density. Boundaries of these squares have zero area.
"""

import argparse
import json
from fractions import Fraction as F
from math import lcm
from pathlib import Path

from verify import bbox, cross, edges, orient, read_point, segments_meet, shifts


def inscribed(x, y, width, height, segments):
    rx, ty = x + width, y + height
    square = [(x, y), (rx, y), (rx, ty), (x, ty)]
    # Show the square is disjoint from the polygon's boundary, and use
    # winding number to check that a point in this connected square is inside.
    winding = 0
    for a, b in segments:
        if a[1] <= y < b[1] and orient(a, b, square[0]) > 0:
            winding += 1
        elif b[1] <= y < a[1] and orient(a, b, square[0]) < 0:
            winding -= 1
        if (max(a[0], b[0]) < x or min(a[0], b[0]) > rx or
                max(a[1], b[1]) < y or min(a[1], b[1]) > ty):
            continue
        if (x <= a[0] <= rx and y <= a[1] <= ty or
                any(segments_meet(a, b, c, d) for c, d in edges(square))):
            return False
    return winding != 0


def check(spec, data, ideal=None):
    U, V = map(read_point, spec['period'])
    W = tuple(v / 3 for v in V)
    raw = [[read_point(c) for c in p['vertices']] for p in spec['pieces']]
    labels = [p['color'] for p in spec['pieces']]
    if len(set(labels)) != 6:
        raise ValueError('All six labels must occur')
    # Row translation permutes the colors. This must hold consistently for
    # all pieces, including wraparound into a different true period.
    permutation = {}
    for i, shape in enumerate(raw):
        for k in (0, 1, -1):
            translated = [(x + W[0] - k * V[0], y + W[1] - k * V[1]) for x, y in shape]
            if translated in raw:
                label = labels[raw.index(translated)]
                if permutation.setdefault(labels[i], label) != label:
                    raise ValueError('Inconsistent one-row symmetry')
                break
        else:
            raise ValueError('Missing one-row symmetry')
    if set(permutation.values()) != set(labels):
        raise ValueError('Row permutation is not bijective')

    side = F(data['side'])
    if side <= 0:
        raise ValueError('Nonpositive square')
    actions = [(F(x), F(y), i, m, n) for x, y, i, m, n in data['assignments']]
    if any(x*x + y*y != 1 for x, y, *_ in actions):
        raise ValueError('A displacement does not have length one')
    den = lcm(side.denominator, *(t.denominator for p in (U, V, W) for t in p),
              *(t.denominator for x, y, *_ in actions for t in (x, y)),
              *(t.denominator for poly in raw for p in poly for t in p))
    at = lambda a: tuple(int(t * den) for t in a)
    u, v, w = map(at, (U, V, W))
    ds = int(side * den)
    det = cross(u, w)
    if det <= 0:
        raise ValueError('Expected positive determinant')
    # For the ideal curved tile, each vertex of the rational polygon is
    # within the stated sup-norm error of the corresponding chord-mesh
    # vertex. The curved tile contains that chord mesh. Along the linear
    # homotopy of corresponding vertices every edge stays this close to
    # its rational counterpart. A rectangle whose padded copy is inside
    # the rational polygon therefore stays inside by winding invariance.
    error = ideal['vertices'] if ideal is not None else F(0)
    period_error = ideal['period_x'] if ideal is not None else F(0)
    def ceil_f(value):
        return -(-value.numerator // value.denominator)
    polygons = [list(map(at, p)) for p in raw]
    segments = list(map(edges, polygons))
    cells = data['cells']
    rows = {}
    offsets = []
    total = 0
    centers = set()
    for cell in cells:
        if len(cell) == 3:
            j, k, choices = cell
            width = 1
        else:
            j, k, width, choices = cell
        if not all(type(t) is int for t in (j, k, width)) or width <= 0:
            raise ValueError('Invalid cell indices or width')
        rows.setdefault(k, []).append((j, j+width))
        total += width
        x, y = j*ds, k*ds
        offsets.extend(((x, y), (x + width*ds, y + ds)))
        covered = set()
        for index in choices:
            a, b, i, m, n = actions[index]
            tx, ty = at((a, b))
            pad = ceil_f((error + abs(m)*period_error)*den)
            if not inscribed(x + tx - m*u[0] - n*v[0] - pad, y + ty - m*u[1] - n*v[1] - pad,
                             width*ds + 2*pad, ds + 2*pad, segments[i]):
                raise ValueError(f'Square not contained at {(x/den, y/den)} action {index}')
            centers.add((tx, ty))
            covered.add(labels[i])
        if covered != set(labels):
            raise ValueError('Missing a color')
    for intervals in rows.values():
        ordered = sorted(intervals)
        if any(a < end for (_,end), (a,_) in zip(ordered, ordered[1:])):
            raise ValueError('Overlapping source cells')
    # Check disjoint source translates and disjoint target translates.
    # A source square itself is completely blank by baseline validity: all
    # six labels have a translated unit witness. Thus source-target boxes
    # may overlap, while the actual source and target rectangles cannot.
    centers.add((0, 0))
    lx, rx, ly, ty = bbox(offsets)
    boxes = [(lx + x, rx + x, ly + y, ty + y) for x, y in sorted(centers)]
    # An ideal image with horizontal lattice coefficient m can overlap
    # another box only when |m| <= x-span / minimal horizontal period.
    # Inflate candidate enumeration by the largest possible shift error.
    if w[0] or u[0] <= period_error*den:
        raise ValueError('Expected a vertical row vector and positive horizontal period')
    span = max(b[1] for b in boxes) - min(b[0] for b in boxes)
    max_m = span // (u[0] - period_error*den)
    enum_pad = ceil_f(max_m * period_error * den)
    zero = sorted(centers).index((0, 0))
    for i, a in enumerate(boxes):
        for j, b in enumerate(boxes[:i+1]):
            if (i == zero) != (j == zero):
                continue
            for m, n, dx, dy in shifts(a, b, u, w, det, enum_pad):
                if i == j and m == n == 0:
                    continue
                reach = ceil_f(abs(m) * period_error * den)
                if a[0] < b[1]+dx+reach and b[0]+dx-reach < a[1] and a[2] < b[3]+dy and b[2]+dy < a[3]:
                    raise ValueError('Ambiguous area charge at overlapping boxes')
    fraction = F(total * ds**2, det)
    if ideal is not None:
        # Round the improved denominator bound down only after division.
        fraction = total * side**2 / (2*ideal['x_hi']*W[1])
        fraction = F((fraction*10**18).__floor__(), 10**18)
    return {'squares_per_A_hole': total, 'strips': len(cells), 'source_square_side': str(side),
            'distinct_translations': len(centers)-1, 'lower_bound': str(fraction),
            'decimal': float(fraction), 'old_label_change_needed_at_target': str(fraction-F(1,10000))}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('pattern', type=Path)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--ideal', action='store_true',
                        help='transfer to the exact curved Parts pattern using the verified chord-mesh enclosures')
    args = parser.parse_args()
    spec = json.loads(args.pattern.read_text())
    ideal = None
    if args.ideal:
        from ideal_proxy import check as check_proxy
        ideal = check_proxy(spec)
    print(json.dumps(check(spec, json.loads(args.certificate.read_text()), ideal), indent=2))

"""Lift a supplied cubic (p,q) colouring to a degree-nine colouring and check it."""
import argparse
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, permutations
import json
from pathlib import Path

PERIOD = Fraction(19, 2)


def validate(vertex_count, edges, degree, p, q):
    stars = [[] for _ in range(vertex_count)]
    pairs = set()
    for u, v, c in edges:
        assert 0 <= u < v < vertex_count and (u, v) not in pairs and 0 <= c < p
        pairs.add((u, v))
        stars[u].append(c)
        stars[v].append(c)
    for star in stars:
        assert len(star) == degree
        for x, y in combinations(star, 2):
            assert q <= (x-y) % p <= p-q


def core_data():
    data = json.loads(Path(__file__).with_name('tripod.json').read_text())
    roots = data['roots']
    edges = [(u,v) for row in data['classes'] for u,v in row] + [(v,13+i) for i,v in enumerate(roots)]
    slots = [c for c,row in enumerate(data['classes']) for _ in row] + [0,6,12]
    following = [set() for _ in edges]
    for i,j in permutations(range(len(edges)),2):
        if (slots[j]-slots[i]) % 19 == 2 and set(edges[i]).intersection(edges[j]):
            following[i].add(j)

    def closure(seeds):
        reached = set(seeds)
        queue = list(seeds)
        while queue:
            for nxt in following[queue.pop()] - reached:
                reached.add(nxt)
                queue.append(nxt)
        return reached

    return edges, slots, closure([59]), closure([58,59])


def extend(core, colours, circle):
    edges, slots, last, last_two = core
    marks = sorted(colours)
    gaps = [(marks[(i+1)%3] - marks[i]) % circle for i in range(3)]
    assert min(gaps) >= 3
    excess = [g-3 for g in gaps]
    left = Fraction(1,2)
    reserved = []
    for arc in excess:
        piece = min(left,arc)
        reserved.append(piece)
        left -= piece
    assert left == 0
    cuts = [0, 3+reserved[0], 6+reserved[0]+reserved[1], PERIOD]
    midpoints = [(x+y)/2 for x,y in zip(cuts,cuts[1:])]
    result = []
    for i, c in enumerate(slots):
        x = (Fraction(c,2) + (i in last)*reserved[1] + (i in last_two)*reserved[0]) % PERIOD
        added = sum(excess[j]-reserved[j] for j in range(3) if x >= midpoints[j])
        result.append((marks[0] + x + added) % circle)
    assert result[-3:] == marks
    return zip(edges,result)


def lift(source):
    p, q, order = source['p'], source['q'], source['vertices']
    assert p > 0 and q > 0
    source_edges = [(min(u,v),max(u,v),c) for u,v,c in source['edges']]
    validate(order,source_edges,3,p,q)
    circle = Fraction(3*p,q)
    assert circle >= PERIOD
    out_p, out_q = circle.numerator, circle.denominator
    out_edges = []
    incident = defaultdict(list)

    def add(u,v,colour):
        out_edges.append([min(u,v),max(u,v),int(out_q * (colour % circle))])

    for u,v,c in source_edges:
        colour = Fraction(3*c,q)
        add(u,v,colour)
        incident[u].append(colour)
        incident[v].append(colour)

    core = core_data()
    for hub in range(order):
        for copy in range(2):
            first = order + 13 * (2*hub + copy)
            marks = [(c+copy+1) % circle for c in incident[hub]]
            for (u,v), colour in extend(core,marks,circle):
                add(first+u, first+v if v<13 else hub, colour)
    validate(27*order,out_edges,9,out_p,out_q)
    return dict(vertices=27*order,p=out_p,q=out_q,edges=out_edges)


def demo():
    # K4 supplies inexpensive legal source colourings to exercise the lift.
    # Exact-index source graphs for the theorem come from Lukoťka and Mazák.
    for p,q in [(19,6),(16,5),(45,14),(173,54),(29,9)]:
        colours = [0,p//3,(2*p)//3]
        edges = [[u,v,colours[(u^v)-1]] for u,v in combinations(range(4),2)]
        result = lift(dict(vertices=4,p=p,q=q,edges=edges))
        print(f"Checked all {len(result['edges'])} edges on the "
              f"({result['p']},{result['q']}) grid.")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source',nargs='?',type=Path,help='JSON with vertices, p, q and [u,v,colour] edges')
    args = parser.parse_args()
    if args.source:
        print(json.dumps(lift(json.loads(args.source.read_text()))))
    else:
        demo()

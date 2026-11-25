"""Verify the affine colourings, four simple graphs, and exact fractional indices."""
from fractions import Fraction
from itertools import combinations


# Edge order is lexicographic on the nine-vertex core, then its two pendant edges.
ENDS = {
    1: ([6,9,16,12,3,1,18,12,4,15,4,15,7,18,10,13,3,0,9,16,10,1,7,6,0,13,0,7],
        [2,3,5,4,1,0,6,4,1,5,1,5,2,6,3,4,1,0,3,5,3,0,2,2,0,4,0,2]),
    2: ([13,3,10,16,7,5,16,-1,13,2,15,4,12,18,9,1,9,1,12,18,7,-1,10,6,15,4,0,8],
        [4,1,3,5,2,1,5,-1,4,0,5,1,4,6,3,0,3,0,4,6,2,-1,3,2,5,1,0,2]),
}


def block(t):
    paths = {
        1: [[0,1], [0,2,3,1], [0,4,5,6,7,8,1]],
        2: [[0,1], [0,2,1], [0,3,4,5,6,7,8,1]],
        3: [[0,2,1], [0,3,4,0], [1,5,6,7,8,1]],
    }
    omitted = set()
    for path in paths[t]:
        omitted.update(tuple(sorted(pair)) for pair in zip(path, path[1:]))
    return [e for e in combinations(range(9), 2) if e not in omitted] + [(0, 9), (1, 10)]


def check_affine(t):
    edges = block(t)
    lo, hi = ENDS[t]
    assert len(edges) == len(lo) == len(hi) == 28
    assert lo[-2:] == [0, 6+t] and hi[-2:] == [0, 2]
    for j, e in enumerate(edges):
        for i, f in enumerate(edges[:j]):
            if set(e).intersection(f):
                x, y = lo[j]-lo[i], hi[j]-hi[i]
                assert x*y > 0 and 3 <= abs(x) <= 17 and 1 <= abs(y) <= 6
    # Every cut splitting this core already costs at least five internal edges.
    for mask in range(1, 2**9-1):
        assert sum(((mask >> u) ^ (mask >> v)) & 1 for u, v in edges[:-2]) >= 5


def check_ring(types):
    q = 1+sum(types)
    p = 7*q-1
    offset = 0
    graph = {}
    for i, t in enumerate(types):
        edges = block(t)
        lo, hi = ENDS[t]
        # The interpolation parameter at 7-1/q is 1-3/q.
        slots = [(x+(q-3)*y+offset) % p for x, y in zip(lo, hi)]
        for (u, v), c in zip(edges[:-2], slots[:-2]):
            graph[9*i+u, 9*i+v] = c
        u, v = 9*i+1, 9*((i+1)%3)
        graph[tuple(sorted((u,v)))] = slots[-1]
        assert slots[-2] == offset % p
        offset += 2*q+t
    assert offset == p and len(graph) == 81
    adjacent = [set() for _ in range(27)]
    for u, v in graph:
        assert 0 <= u < v < 27
        adjacent[u].add(v)
        adjacent[v].add(u)
    reached = {0}
    queue = [0]
    for u in queue:
        colours = sorted(graph[tuple(sorted((u, v)))] for v in adjacent[u])
        assert len(colours) == 6
        assert min(b-a for a,b in zip(colours, colours[1:]+[colours[0]+p])) >= q
        for v in adjacent[u]-reached:
            reached.add(v)
            queue.append(v)
    assert len(reached) == 27 and Fraction(p, q) == 7-Fraction(1,q)
    print(f"{types} has a directly checked ({p},{q}) colouring on 27 vertices")


def grid_audit():
    """Deduce the four sharp lower bounds by deleting unused slots."""
    from functools import lru_cache

    @lru_cache(None)
    def separation(value, kind):
        p, q = value.numerator, value.denominator
        if value == Fraction(20, 3):
            return 6+kind
        d = pow(p, -1, q)
        c = (p*d-1)//q
        assert c*q == p*d-1 and Fraction(c,d) >= Fraction(20,3)
        needed = separation(Fraction(c,d), kind)
        assert p > 28 or value == Fraction(27,4)
        empty = max(1, p-28)
        for h in range(p):
            lo, up_count = divmod(c*h, p)
            if lo+int(up_count >= empty) >= needed:
                return h
        raise RuntimeError("no surviving difference")

    possible = {Fraction(p,q) for q in range(1,14) for p in range(1,82)}
    for k in range(4):
        q = 4+k
        target = 7-Fraction(1,q)
        predecessor = max(x for x in possible if x < target)
        low = [separation(predecessor,t) for t in [1,2]]
        assert (3-k)*low[0]+k*low[1] > predecessor.numerator
        print(f"The projection to {predecessor} gives separation bounds {low}")


HALF = {
    2: [9,2,7,11,5,4,11,0,9,2,10,3,8,12,6,1,6,1,8,12,5,0,7,4,10,3,0,6],
    3: [4,11,6,2,8,2,10,8,0,9,3,5,1,7,12,0,4,11,6,7,12,5,1,9,3,10,0,6],
}


def longer_rings():
    for kind, row in HALF.items():
        edges = block(kind)
        assert len(row) == len(edges) == 28 and row[-2:] == [0,6]
        for i,j in combinations(range(28),2):
            if set(edges[i]).intersection(edges[j]):
                early = row[i]-row[j]
                assert 2 <= abs(early) <= 11
                if kind == 2:
                    late = ENDS[2][1][i]-ENDS[2][1][j]
                    assert early*late > 0 and 1 <= abs(late) <= 6
    denominators = set()
    for k in range(1,6):
        length = 2*k+1
        for b in range(length+1):
            deficit = Fraction(k-3+b,k+2*b)
            if not 0 < deficit < Fraction(1,2):
                continue
            r = 7-deficit
            p, q = r.numerator, r.denominator
            a = deficit.numerator
            origin = 0
            graph = {}
            for i in range(length):
                kind = 2 if i < b else 3
                if kind == 2:
                    slots = [a*u+(q-2*a)*v for u,v in zip(HALF[2],ENDS[2][1])]
                else:
                    # Floor the fixed half-grid colouring after scaling by q.
                    slots = [q*u//2 for u in HALF[3]]
                edges = block(kind)
                for (u,v), c in zip(edges[:-2], slots[:-2]):
                    graph[9*i+u,9*i+v] = (origin+c)%p
                assert slots[-2] == 0 and slots[-1] == (2*q+2*a if kind == 2 else 3*q)
                origin += slots[-1]
                join = tuple(sorted((9*i+1,9*((i+1)%length))))
                assert join not in graph
                graph[join] = origin%p
            assert origin == k*p and len(graph) == 27*length
            stars = [[] for _ in range(9*length)]
            for (u,v), c in graph.items():
                assert 0 <= u < v < len(stars)
                stars[u].append(c)
                stars[v].append(c)
            for colours in stars:
                colours.sort()
                assert len(colours) == 6
                assert min(y-x for x,y in zip(colours,colours[1:]+[colours[0]+p])) >= q
            denominators.add(q)
    assert sorted(denominators) == [*range(3,14),15,16,17,19,20,21,23,25,27]
    print("Longer odd rings checked for reduced denominators", sorted(denominators))


if __name__ == "__main__":
    for kind in ENDS:
        check_affine(kind)
    for twos in range(4):
        check_ring([1]*(3-twos)+[2]*twos)
    grid_audit()
    longer_rings()

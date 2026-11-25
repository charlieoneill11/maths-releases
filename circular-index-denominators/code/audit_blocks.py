"""Independent SAT replay of the terminal exclusions for the three blocks.

Install python-sat and run python3 audit_blocks.py. Uses the edge lists from
replay_mixed.py and derives slot counts from the window deficit.
"""
from functools import lru_cache
from itertools import combinations, combinations_with_replacement

from pysat.card import CardEnc, EncType, ITotalizer
from pysat.formula import IDPool
from pysat.solvers import Solver

from replay_mixed import block


@lru_cache(None)
def palettes(p, q):
    return [row for row in combinations(range(p), 6)
            if all(b-a >= q for a,b in zip(row, row[1:]+(row[0]+p,)))]


def schedules(p, q, h, all_slots):
    if all_slots:
        for double in range(p):
            yield [1+(c == double)-(c == 0)-(c == h) for c in range(p)]
        return
    for deficits in combinations_with_replacement(range(p),4*p-26*q):
        windows = [4-deficits.count(i) for i in range(p)]
        sizes = [0]*p
        for t in range(p):
            i = t*q % p
            sizes[(i+q)%p] = sizes[i]+windows[(i+1)%p]-windows[i]
        correction, remainder = divmod(26-sum(sizes),p)
        assert remainder == 0
        yield [v+correction for v in sizes]


def verify_difference(kind, p, q, h, full_test=False):
    edges = block(kind)
    pool = IDPool()
    with Solver(name="cadical195") as solver:
        colour = [[pool.id() for _ in range(p)] for edge in edges]

        def at_most_one(literals):
            encoding = CardEnc.atmost(literals, 1, vpool=pool, encoding=EncType.seqcounter)
            solver.append_formula(encoding.clauses)

        def one(literals):
            solver.add_clause(literals)
            at_most_one(literals)

        for row in colour:
            one(row)
        solver.add_clause([colour[-2][0]])
        solver.add_clause([colour[-1][h]])
        for v in range(9):
            incident = [j for j,edge in enumerate(edges) if v in edge]
            occupied = []
            for c in range(p):
                present = pool.id()
                uses = [colour[j][c] for j in incident]
                at_most_one(uses)
                solver.add_clause([-present]+uses)
                for literal in uses:
                    solver.add_clause([-literal,present])
                occupied.append(present)
            for c in range(p):
                for k in range(1,q):
                    solver.add_clause([-occupied[c],-occupied[(c+k)%p]])
            allowed = palettes(p,q)
            selected = [pool.id() for _ in allowed]
            one(selected)
            for c in range(p):
                uses = [literal for literal,row in zip(selected,allowed) if c in row]
                solver.add_clause([-occupied[c]]+uses)
                for literal in uses:
                    solver.add_clause([-literal,occupied[c]])

        # In the totalizer rhs[j] becomes true if at least j+1 core edges use the slot.
        bounds = []
        for c in range(p):
            tree = ITotalizer([row[c] for row in colour[:-2]], ubound=4, top_id=pool.top)
            solver.append_formula(tree.cnf.clauses)
            pool.top = tree.top_id
            bounds.append(tree.rhs[:])
            tree.delete()
        count = 0
        for sizes in schedules(p,q,h,p == 27 and not full_test):
            if min(sizes) < 0:
                continue
            assert sum(sizes) == 26
            windows = [sum(sizes[(i+k)%p] for k in range(q)) for i in range(p)]
            if any(2*w+sum((c-i)%p < q for c in (0,h)) > 9 for i,w in enumerate(windows)):
                continue
            if full_test:
                # Every empty-slot projection must keep the certified (20,3) separation.
                empty = [c for c,s in enumerate(sizes) if s == 0 and c not in (0,h)]
                if any((20*((-c)%p+h))//p-(20*((-c)%p))//p < 9 for c in empty):
                    continue
            count += 1
            assumptions = [-bounds[c][value] for c,value in enumerate(sizes)]
            if solver.solve(assumptions=assumptions):
                raise ValueError(f"Unexpected colouring for block {kind} at {(p,q,h)}")
    return count


def mixed_audit():
    for p,q,expected in [(20,3,1932), (27,4,66)]:
        count = 0
        for kind in [1,2]:
            last = 5+kind if p == 20 else p//2
            for h in range(last+1):
                count += verify_difference(kind,p,q,h)
        assert count == expected
        print(f"{count} schedules excluded independently at ({p},{q})", flush=True)


def third_audit():
    count = sum(verify_difference(3,20,3,h) for h in range(9))
    assert count == 1281
    count = sum(verify_difference(3,27,4,h) for h in range(14))
    assert count == 33
    assert verify_difference(3,27,4,11,full_test=True) == 70
    print("Third block passed 1,281 third-grid, 33 all-slots, and 70 projection tests", flush=True)


if __name__ == "__main__":
    mixed_audit()
    third_audit()

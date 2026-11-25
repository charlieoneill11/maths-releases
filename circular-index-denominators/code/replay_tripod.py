"""Audit the scaling block, its three terminal perturbations and its half-grid table."""
import argparse
import itertools
import json
from collections import defaultdict
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory


def certificate():
    data = json.loads(Path(__file__).with_name("tripod.json").read_text())
    roots = data["roots"]
    edges = [tuple(e) for row in data["classes"] for e in row]
    slots = [c for c, row in enumerate(data["classes"]) for _ in row]
    assert len(edges) == len(set(edges)) == 57
    assert len(set(roots)) == 3
    edges += [(v, 13 + j) for j, v in enumerate(roots)]
    slots += [0, 6, 12]
    stars = defaultdict(list)
    for i, (v, w) in enumerate(edges):
        assert 0 <= v < w < 16
        stars[v].append(i)
        stars[w].append(i)
    assert [len(stars[v]) for v in range(16)] == [9] * 13 + [1] * 3

    def check(colours):
        for incident in stars.values():
            for i, j in itertools.combinations(incident, 2):
                assert 2 <= (colours[i] - colours[j]) % 19 <= 17

    check(slots)
    successors = [set() for _ in edges]
    for incident in stars.values():
        for i, j in itertools.permutations(incident, 2):
            if (slots[j] - slots[i]) % 19 == 2:
                successors[i].add(j)

    def closure(seeds):
        reached = set(seeds)
        queue = list(seeds)
        while queue:
            i = queue.pop()
            for j in successors[i] - reached:
                reached.add(j)
                queue.append(j)
        return reached

    one = closure([59])
    two = closure([58, 59])
    assert one <= two
    assert one & {57, 58, 59} == {59}
    assert two & {57, 58, 59} == {58, 59}
    for moved, expected in ((one, [0, 6, 13]), (two, [0, 7, 13])):
        shifted = [(c + (i in moved)) % 19 for i, c in enumerate(slots)]
        assert shifted[-3:] == expected
        check(shifted)
    return roots, edges


def gap_types():
    return [(x, y, 19 - x - y) for x in range(2, 7) for y in range(x, 19)
            if y <= 19-x-y]


def formula(edges, gaps):
    from pysat.card import CardEnc, EncType
    from pysat.formula import CNF, IDPool

    gaps_x, gaps_y, _ = gaps
    terminal = (0, gaps_x, gaps_x + gaps_y)
    omitted = {(c + off) % 19 for c in terminal for off in (0, -1)}
    palettes = {h: {(h + 2 * j) % 19 for j in range(1, 10)}
                for h in range(19) if h not in omitted}
    ids = IDPool()
    clauses = CNF()

    def lit(*key):
        return ids.id(key)

    def at_most_one(literals):
        if len(literals) > 1:
            clauses.extend(CardEnc.atmost(literals, 1, vpool=ids, encoding=EncType.seqcounter))

    def exactly_one(literals):
        clauses.append(literals)
        at_most_one(literals)

    for v in range(13):
        exactly_one([lit("hole", v, h) for h in palettes])
    for h in palettes:
        exactly_one([lit("hole", v, h) for v in range(13)])
    incident = defaultdict(list)
    choices = [range(19) if i < 57 else terminal for i in range(60)]
    for i, (v, w) in enumerate(edges):
        incident[v].append(i)
        incident[w].append(i)
        exactly_one([lit("edge", i, c) for c in choices[i]])
    for c in terminal:
        exactly_one([lit("edge", i, c) for i in range(57, 60)])
    for v in range(13):
        for c in range(19):
            at_most_one([lit("edge", i, c) for i in incident[v] if c in choices[i]])
        for h, palette in palettes.items():
            for i in incident[v]:
                for c in set(choices[i]) - palette:
                    clauses.append([-lit("hole", v, h), -lit("edge", i, c)])
    for v, w in edges[:57]:
        for h in palettes:
            if h + 1 in palettes:
                clauses.append([-lit("hole", v, h), -lit("hole", w, h+1)])
                clauses.append([-lit("hole", w, h), -lit("hole", v, h+1)])
    return clauses


def audit(edges, checker):
    from pysat.solvers import Solver

    with TemporaryDirectory() as directory:
        cnf = Path(directory) / "case.cnf"
        proof = Path(directory) / "case.drat"
        for gaps in gap_types():
            clauses = formula(edges, gaps)
            with Solver(name="g42", bootstrap_with=clauses, with_proof=bool(checker)) as solver:
                possible = solver.solve()
                assert possible == (gaps in ((5, 7, 7), (6, 6, 7))), gaps
                if checker and not possible:
                    clauses.to_file(cnf)
                    proof.write_text("\n".join(solver.get_proof()) + "\n")
                    result = subprocess.run([str(checker), str(cnf), str(proof)],
                                            capture_output=True, check=True)
                    assert b"s VERIFIED" in result.stdout
            print(gaps, "SAT" if possible else "UNSAT", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sat", action="store_true")
    parser.add_argument("--drat-trim", type=Path)
    parser.add_argument("--emit", action="store_true", help="emit the independent C++ checker's input")
    args = parser.parse_args()
    roots, edges = certificate()
    if args.emit:
        print(*roots)
        for edge in edges[:57]:
            print(*edge)
    else:
        print("All three terminal assignments and the nested perturbations verified.")
    if args.sat or args.drat_trim:
        audit(edges, args.drat_trim.resolve() if args.drat_trim else None)

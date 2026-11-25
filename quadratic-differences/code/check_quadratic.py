"""Independent checks for the paper on four-colour quadratic van der Waerden numbers.

Usage:
    python3 check_quadratic.py FOLDER DRAT_TRIM [KISSAT]

FOLDER is the problem folder (it holds thresholds.json, grid-tile.txt, the
certificates/ directory and the encoders encode.py and forcing.py). DRAT_TRIM is
a compiled drat-trim. With KISSAT (version 4.0.4), the script also re-solves the
formula of Proposition 8 and checks the new proof.

The script was written separately from the programs in FOLDER. It takes the
words, the tile and the sixteen configurations from the paper, builds every CNF
formula from the definitions, compares each with the formula produced by the
folder's encoders as a set of clauses, and runs drat-trim on the stored proofs
against its own formulas. Standard library only; needs Python 3.10+ and xz.
"""
import gzip
import itertools
import json
import lzma
import subprocess
import sys
import tempfile
from pathlib import Path

# ---------------------------------------------------------------- paper data
WORDS = {  # Table 3: colours of 0, 1, ..., W-2
    0: (58, "013210130121301212032120323213232130301303012030" "120103201"),
    1: (97, "021332102200330123021332213211330023021132213211"
            "330023102300213211330023102100213311021032102100"),
    2: (82, "010121232020131202313020202313020202313030202313" "131202313131202323030101313020131"),
    3: (81, "021120330211203302112033022033021120330211203302" "11203311203302112033021120330211"),
    4: (75, "022133300221330001212300011222003112220331122233" "30121233300111330001113200"),
    5: (89, "001312312123001231232300123123230000123123000012" "3123000012323123001232312300123131231200"),
    6: (73, "022211333300022111133300222211133000022211333300" "022111133300222211133000"),
    7: (49, "020202101010313131232323020202101010313131232323"),
    8: (53, "000000111111133333322222220000000111111333333322" "2222"),
}
TILE = [  # Proposition 7, row u mod 8, column v mod 16
    "0100222222133331", "2223131313122122", "1113132200003031", "0000000132313130",
    "2213333101002222", "1312212222231313", "0000303111131322", "3231313000000001",
]
CONFIGURATIONS = [  # Table 1, coarse coordinates (x, y)
    [(0,0),(0,2),(0,6),(1,3),(1,5),(1,7),(1,9),(2,0)],
    [(0,0),(0,2),(1,3),(1,5),(1,7),(1,9),(2,0),(2,2)],
    [(0,0),(0,6),(1,3),(1,5),(1,7),(1,9),(2,0),(2,6)],
    [(0,0),(1,3),(1,5),(1,7),(1,9),(2,0),(2,2),(2,6)],
    [(0,3),(0,7),(0,9),(1,0),(1,2),(1,4),(1,6),(2,9)],
    [(0,3),(0,9),(1,0),(1,2),(1,4),(1,6),(2,3),(2,9)],
    [(0,7),(0,9),(1,0),(1,2),(1,4),(1,6),(2,7),(2,9)],
    [(0,9),(1,0),(1,2),(1,4),(1,6),(2,3),(2,7),(2,9)],
    [(0,0),(0,2),(0,6),(0,8),(1,1),(1,3),(1,5),(1,7),(2,0),(2,8)],
    [(0,0),(0,2),(0,8),(1,1),(1,3),(1,5),(1,7),(2,0),(2,2),(2,8)],
    [(0,0),(0,6),(0,8),(1,1),(1,3),(1,5),(1,7),(2,0),(2,6),(2,8)],
    [(0,0),(0,8),(1,1),(1,3),(1,5),(1,7),(2,0),(2,2),(2,6),(2,8)],
    [(0,1),(0,3),(0,7),(0,9),(1,2),(1,4),(1,6),(1,8),(2,1),(2,9)],
    [(0,1),(0,3),(0,9),(1,2),(1,4),(1,6),(1,8),(2,1),(2,3),(2,9)],
    [(0,1),(0,7),(0,9),(1,2),(1,4),(1,6),(1,8),(2,1),(2,7),(2,9)],
    [(0,1),(0,9),(1,2),(1,4),(1,6),(1,8),(2,1),(2,3),(2,7),(2,9)],
]


def require(test, message):
    if not test:
        raise SystemExit("FAILED: " + message)


# ---------------------------------------------------------------- formulas
def colouring_cnf(n, edges):
    """Exactly one colour per vertex and no monochromatic edge (variable 4v+c+1: vertex v has colour c)."""
    var = lambda v, c: 4 * v + c + 1
    cls = [tuple(var(v, c) for c in range(4)) for v in range(n)]
    cls += [(-var(v, a), -var(v, b)) for v in range(n) for a, b in itertools.combinations(range(4), 2)]
    return cls + [(-var(a, c), -var(b, c)) for a, b in edges for c in range(4)]


def merge(mine, theirs, edges):
    """Compare the folder's formula with ours, apart from its two symmetry-breaking unit clauses.

    Those must name two different colours at the two ends of an edge; that is valid because
    the ends of an edge get different colours, and colours can be renamed. We keep the
    folder's units, so that the stored proofs apply, and our own other clauses."""
    units = sorted(c for c in theirs if len(c) == 1)
    rest = [c for c in theirs if len(c) > 1]
    require(len(rest) == len(mine) and as_set(rest) == as_set(mine), "formula differs from the folder's")
    require(len(units) == 2 and all(c[0] > 0 for c in units), "two positive unit clauses")
    (va, ca), (vb, cb) = (divmod(c[0] - 1, 4) for c in units)
    require(ca != cb and tuple(sorted((va, vb))) in {tuple(sorted(e)) for e in edges},
            "unit clauses must name two colours at the ends of an edge")
    return mine + units


def as_set(clauses):
    return {tuple(sorted(c)) for c in clauses}


def read_dimacs(text):
    lines = text.split("\n")
    header = lines[0].split()
    require(header[:2] == ["p", "cnf"], "DIMACS header")
    clauses = [tuple(int(t) for t in line.split()[:-1]) for line in lines[1:] if line.strip()]
    require(len(clauses) == int(header[3]), "DIMACS clause count")
    return int(header[2]), clauses


def write_dimacs(path, nvars, clauses):
    with open(path, "w") as out:
        out.write(f"p cnf {nvars} {len(clauses)}\n")
        for c in clauses:
            out.write(" ".join(map(str, c)) + " 0\n")


def run_encoder(folder, *args):
    out = subprocess.run([sys.executable, "-B", *args], cwd=folder, check=True,
                         capture_output=True, text=True).stdout
    return read_dimacs(out)


def drat_check(drat_trim, cnf, proof, label):
    result = subprocess.run([drat_trim, str(cnf), str(proof)], capture_output=True, text=True)
    require("s VERIFIED" in result.stdout.replace("\r", "\n").splitlines(), f"drat-trim on {label}")
    print(f"  {label}: drat-trim reports s VERIFIED")


# ---------------------------------------------------------------- 1. thresholds
def distances(j, limit):
    """All |d^2 + jd| in 1..limit, by direct enumeration of d."""
    bound = limit + j + 2
    return {abs(d * d + j * d) for d in range(-bound, bound + 1)} - {0} & set(range(1, limit + 1))


def check_thresholds(folder, drat_trim, scratch):
    data = json.loads((folder / "thresholds.json").read_text())
    print("1. thresholds")
    for row in data:
        j, w = row["j"], row["W"]
        require(WORDS[j] == (w, row["colouring"]), f"paper word differs from thresholds.json, j={j}")
        word = row["colouring"]
        require(len(word) == w - 1 and set(word) <= set("0123"), f"word shape j={j}")
        dist = distances(j, w)
        require(all(word[a] != word[a + k] for k in dist for a in range(len(word) - k)), f"word j={j}")
        edges = [(a, a + k) for k in sorted(dist) for a in range(w - k)]
        nvars, theirs = run_encoder(folder, "encode.py", "interval", str(j), str(w))
        require(nvars == 4 * w, f"variables, j={j}")
        formula = merge(colouring_cnf(w, edges), theirs, edges)
        cnf, proof = scratch / f"j{j}.cnf", scratch / f"j{j}.drat"
        write_dimacs(cnf, 4 * w, formula)
        proof.write_bytes(gzip.decompress((folder / "certificates" / f"j{j}.drat.gz").read_bytes()))
        print(f"  j={j}: word of length {w - 1} proper, {len(edges)} edges at W={w}, formula matches")
        drat_check(drat_trim, cnf, proof, f"W(x^2+{j}x;4) <= {w}")


# ---------------------------------------------------------------- 2. lattice graphs
def lattice_edges(points, kmax):
    index = {p: i for i, p in enumerate(points)}
    edges = []
    for i, (u, v) in enumerate(points):
        for d in range(1, kmax + 1):
            for s in (1, -1):
                k = index.get((u + d, v + s * d * d))
                if k is not None:
                    edges.append((i, k))
    return edges


def check_tile(folder):
    print("2. tile (Proposition 7)")
    require((folder / "grid-tile.txt").read_text().split() == TILE, "paper tile differs from grid-tile.txt")
    colour = lambda u, v: TILE[u % 8][v % 16]
    require(all(colour(u, v) != colour(u + d, v + s * d * d)
                for u in range(8) for v in range(16) for d in range(1, 8) for s in (1, -1)),
            "tile is not proper")
    print("  the 8 x 16 tile is a proper colouring of Gamma_7 (1792 comparisons)")


def crop_points():
    return [(u, v) for u in range(11) for v in range(65) if (u + v) % 2 == 0
            and (v != 0 or u >= 8) and (v != 64 or u <= 2)]


def check_crop(folder, drat_trim, kissat, scratch):
    print("3. cropped rectangle S (Proposition 8, Corollary 9)")
    pts = crop_points()
    edges = lattice_edges(pts, 8)
    require((len(pts), len(edges)) == (350, 2362), "size of S")
    require(sorted((pts[a], pts[b]) for a, b in edges if abs(pts[a][0] - pts[b][0]) == 8)
            == [((0, 64), (8, 0)), ((2, 64), (10, 0))], "d = 8 edges of S")
    nvars, theirs = run_encoder(folder, "encode.py", "crop")
    formula = merge(colouring_cnf(len(pts), edges), theirs, edges)
    require(nvars == 1400 and len(formula) == 11900, "crop formula size")
    print("  350 vertices, 2362 edges, 1400 variables, 11900 clauses; formula matches")
    # Bounds on the labels: brute force against the formula of Corollary 9.
    for E in range(0, 30):
        for F in range(0, 30):
            if E == F == 0:
                continue
            labels = [F * u + E * v for u, v in pts]
            m = min(8 * F, E + F, 2 * E)
            require(min(labels) == m and max(labels) == 64 * E + 10 * F - m, "label range of S")
    print("  min and max of Fu+Ev on S agree with Corollary 9 for 0 <= E, F < 30")
    if kissat:
        cnf, proof = scratch / "crop.cnf", scratch / "crop.drat"
        write_dimacs(cnf, 1400, formula)
        status = subprocess.run([kissat, str(cnf), str(proof)], stdout=subprocess.DEVNULL).returncode
        require(status == 20, "Kissat did not report UNSAT on S")
        drat_check(drat_trim, cnf, proof, "Gamma_8[S] not four-colourable (fresh Kissat proof)")
        proof.unlink()
    else:
        print("  (no Kissat given: the refutation of S was not re-solved)")


# ---------------------------------------------------------------- 3. the near-axis lemmas
def phi(x, y):
    return (x % 2, ((y - x) // 2) % 2)


COARSE = [(d, s * d * d) for d in (1, 2, 3) for s in (1, -1)]


def check_configurations():
    print("4. forcing configurations (Lemma 15)")
    seen = set()
    for U in CONFIGURATIONS:
        parity = (U[0][0] + U[0][1]) % 2
        require(all(0 <= x <= 2 and 0 <= y <= 9 and (x + y) % 2 == parity for x, y in U), "shape")
        require(len({phi(*s) for s in U}) == 4 and len(U) in (8, 10), "configuration meets 4 classes")
        box = {(x, y) for x in range(-6, 9) for y in range(10) if (x + y) % 2 == parity}
        nbrs = {s: [(s[0] + a, s[1] + b) for a, b in COARSE + [(-a, -b) for a, b in COARSE]
                    if (s[0] + a, s[1] + b) in box] for s in box}
        # Colours are named by the classes of phi; renaming colours does not matter.
        colour = {s: phi(*s) for s in U}
        changed = True
        while changed:
            changed = False
            for s in box:
                seen_colours = {colour[t] for t in nbrs[s] if t in colour}
                require(s not in colour or colour[s] not in seen_colours, "contradiction in propagation")
                if s not in colour and len(seen_colours) == 3:
                    (colour[s],) = {(0, 0), (0, 1), (1, 0), (1, 1)} - seen_colours
                    changed = True
        block = [(x, y) for x in range(3) for y in range(10) if (x + y) % 2 == parity]
        require(len(block) == 15 and all(colour.get(s) == phi(*s) for s in block),
                "configuration does not force the block")
        seen.add(frozenset(U))
    require(len(seen) == 16, "sixteen distinct configurations")
    print("  each of the 16 configurations forces the 15-point block to the prescribed colouring")


def check_window_lemmas():
    print("5. Lemma 11 and the kernel vector of Lemma 14, for 1 <= q, 6q <= p <= 120")
    from math import gcd
    bases = [(u0, v0) for u0 in range(8) for v0 in range(2, 20) if (u0 + v0) % 2 == 0]
    require(len(bases) == 72, "72 base points")
    for q in range(1, 21):
        for p in range(6 * q, 121):
            N = 57 * p + 11 * q
            for u0, v0 in bases:
                z = q * u0 + p * v0
                lo, hi = z - 2 * p, z + 38 * p + 4 * q
                require(0 <= lo and hi <= N, "window inside [0, N]")
                lab = lambda x, y: z + 2 * q * x + 4 * p * y
                for x in range(0, 3):
                    active = [y for y in range(-50, 60) if lo <= lab(x, y) <= hi]
                    require(active == list(range(10)), "block rows")
                require(all(lo <= lab(x, y) <= hi for x in range(-6, 9) for y in range(10)), "box")
            K, M = 4 * p + 2 * q, 8 * p
            g = gcd(K, M)
            kappa = (M // g, M // g - 2 * K // g)
            require(2 * q * kappa[0] + 4 * p * kappa[1] == 0 and kappa[0] > 0, "kernel vector")
            require(sum(kappa) % 2 == 0 and phi(*kappa) != (0, 0), "kernel vector outside 2L")
    print("  window, block rows, box and kernel vector verified")


def check_near_axis_formula(folder, drat_trim, scratch):
    print("6. formula of Lemma 16")
    pts = [(u, v) for u in range(12) for v in range(58) if (u + v) % 2 == 0]
    index = {p: i for i, p in enumerate(pts)}
    edges = lattice_edges(pts, 7)
    require((len(pts), len(edges)) == (348, 2352), "size of R")
    mine = colouring_cnf(len(pts), edges)
    bases = [(u0, v0) for u0 in range(8) for v0 in range(2, 20) if (u0 + v0) % 2 == 0]
    classes = [(0, 0), (0, 1), (1, 0), (1, 1)]
    for u0, v0 in bases:
        for U in CONFIGURATIONS:
            for perm in itertools.permutations(range(4)):
                pi = dict(zip(classes, perm))
                mine.append(tuple(-(4 * index[u0 + 2 * x, v0 + 4 * y] + pi[phi(x, y)] + 1) for x, y in U))
    nvars, theirs = run_encoder(folder, "forcing.py", "cnf", "12", "58")
    formula = merge(mine, theirs, edges)
    require(nvars == 1392 and len(formula) == 39494, "size of the formula")
    print("  348 vertices, 2352 edges, 27648 configuration clauses; formula matches")
    cnf, proof = scratch / "near-axis.cnf", scratch / "near-axis.drat"
    write_dimacs(cnf, 1392, formula)
    proof.write_bytes(lzma.decompress((folder / "certificates" / "near-axis.drat.xz").read_bytes()))
    drat_check(drat_trim, cnf, proof, "Lemma 16 (stored proof)")


# ---------------------------------------------------------------- 4. the case analysis
def check_cases():
    print("7. case analysis of Theorem 1 for 0 <= E, F <= 400")
    table = {j: w for j, (w, _) in WORDS.items()}
    for E in range(0, 401):
        for F in range(0, 401):
            if E == F == 0:
                continue
            if E == 0:
                bound = 4 * F
            elif F == 0:
                bound = 57 * E
            elif F % E == 0 and 1 <= F // E <= 8:
                bound = E * (table[F // E] - 1)
            elif E >= 6 * F:
                bound = 57 * E + 11 * F
            else:
                bound = 64 * E + 10 * F - 2 * min(8 * F, E + F, 2 * E)
            require(bound <= 57 * E + 39 * F, f"case analysis at E={E}, F={F}")
    print("  every case gives W - 1 <= 57E + 39F")


def main():
    if len(sys.argv) not in (3, 4):
        raise SystemExit(__doc__)
    folder, drat_trim = Path(sys.argv[1]).resolve(), sys.argv[2]
    kissat = sys.argv[3] if len(sys.argv) == 4 else None
    with tempfile.TemporaryDirectory() as tmp:
        scratch = Path(tmp)
        check_thresholds(folder, drat_trim, scratch)
        check_tile(folder)
        check_crop(folder, drat_trim, kissat, scratch)
        check_configurations()
        check_window_lemmas()
        check_near_axis_formula(folder, drat_trim, scratch)
        check_cases()
    print("all checks passed")


if __name__ == "__main__":
    main()

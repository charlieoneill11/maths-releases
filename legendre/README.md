# Primes between consecutive 11/5-th powers

**Result.** For every positive integer n, the interval (n^(11/5), (n+1)^(11/5)) contains a prime. Along the way, Legendre's conjecture (a prime between consecutive squares) is verified for every m ≤ 10¹⁴. The analytic part uses the Riemann hypothesis, now proved by Alpöge (see the paper).

**Status of the evidence.** The finite range rests on a 2026 cloud computation whose 51.69 TB archive is in private storage. From this repository anyone can check the analytic part (every real x ≥ 3.5 × 10¹³) and the finite results for every n ≤ 3,883,865,444,451 and every m ≤ 70,500,002,100,000 (with the published computation of Sorenson and Webster), plus some isolated ranges. For the other bases below 3.5 × 10¹³ and up to 10¹⁴ the results rest on the verification done inside the run and on its audit. A referee with read access has replayed 1.6 × 10⁸ of the run's checks. So the two theorems are proved by the computation described in the paper, but they have not been verified independently in full. The section "Status of the evidence" in the paper gives the details and the steps of the full pilot replay, which is still open.

- Paper: [legendre.pdf](legendre.pdf). The LaTeX source is in [paper/](paper/) and builds with `pdflatex main.tex`, run twice.
- [research/](research/): the programs that check the analytic statements.
- [computation/](computation/): the finite verification, its retained certificates and the record of the 2026 cloud run.
- Formal proof: [lean/](lean/). Theorem 4 (every real x ≥ 3.5·10¹³) is proved in Lean 4 with Mathlib from the Riemann hypothesis and five published results, and Theorems 1 and 2 also from the computation; see "Formal proof in Lean" below and Appendix H of the paper.

## Analytic part

You need Python 3.10 or later, with assertions enabled (do not use `-O`). Run from `research/`. None of these programs uses the network.

| Command | Reads | What it checks | Needs | Time |
| --- | --- | --- | --- | --- |
| `python3 -B check_classical_bridge.py` | only its own modules | the twelve-mode theorem for every real x ≥ 3.5 × 10¹³ in exact rational arithmetic: the kernel constants, the two slabs, the explicit-formula error budget on [3.5 × 10¹³, 6 × 10¹⁴], and the comparison with Carneiro–Milinovich–Soundararajan for x ≥ 6 × 10¹⁴ | standard library | 20 s |
| `python3 -B check_classical_bridge_arb.py` | nothing | the same theorem, programmed separately in ball arithmetic: the kernel bounds on a different grid, the shoulder charge and margins of both slabs, the error budget on [3.5 × 10¹³, 6 × 10¹⁴] including hypothesis (H), and the comparison for x ≥ 6 × 10¹⁴ | `python-flint` | 3 s |
| `python3 -B check_outer_theorem.py` | the three data files in [research/DATA.md](research/DATA.md) | the sharper cutoff, part (b) of the appendix theorem: every real x ≥ 32,654,578,787,390. This uses the first 1.4 × 10⁶ zeros of ζ and the table of maximal prime gaps up to 1.32 × 10²⁰, whose completeness rests on an exhaustive search not published in a refereed journal. Not used in the proof of the main theorem | NumPy | 2 min |
| `python3 -B check_outer_theorem.py --reduced-inputs` | the gap histogram and `cofactor_gap_prices.json` (not the zeros) | part (a) of the appendix theorem, with neither the zeros nor the maximal-gap table: every real x ≥ 32,746,701,927,355 with the complete prime-gap histogram below 4 × 10¹⁸, and x ≥ 32,971,281,678,698 with no prime-gap data; also x ≥ 32,706,763,162,237 using the histogram and only the maximal gaps below 2⁶⁴ (the search up to 2⁶⁴ is not refereed either) | NumPy | 3.5 min |

`check_outer_theorem.py` prints `Every real x >= 32654578787390 has a prime strictly between x^(11/5) and (x+1)^(11/5).`

## Finite verification

The 2026 computation covered every base below 3.5 × 10¹³: 319,488 shards, 59,162,481,759,320 production checks, run on 22–23 November 2026. Its archive is private, so these checks cannot be replayed from this repository. [computation/COVERAGE.md](computation/COVERAGE.md) is the ledger of all ranges, and [computation/cloud/baseten_prime_pilot/README.md](computation/cloud/baseten_prime_pilot/README.md) describes the run, its schedule, what its audit reads and checks, and what has been replayed independently.

The certificates kept in this repository (from earlier runs) are checked by

```sh
cd computation
sha256sum -c evidence.sha256
bash replay.sh
```

The first command checks the 65 non-Markdown files of `computation/` against their recorded digests. The second reads only files in `computation/`, needs `g++` with C++17, GMP with its C++ interface (`libgmp-dev` on Debian and Ubuntu), gzip and Python 3, and takes about two minutes. It verifies every retained witness and Pratt certificate (15,018,635 power rows, 4,000,000 square rows and 1,100,000 Oppermann pairs), recomputes the coverage credits, and ends by printing the remaining workloads of the 3.5 × 10¹³ plan. This establishes the finite results for every n ≤ 3,883,865,444,451 and every m ≤ 70,500,002,100,000 and on the isolated ranges listed in [computation/README.md](computation/README.md#what-the-public-files-establish), and nothing about the other bases.

All the commands above were re-run from this folder on 24 November 2026 and passed.

## Formal proof in Lean

The folder [lean/](lean/) holds a Lean 4 development, pinned to Lean v4.29.1 and Mathlib v4.29.1. [lean/Legendre/Statement.lean](lean/Legendre/Statement.lean) states Theorems 1, 2 and 4 of the paper. The public theorems are

```lean
Legendre.outer_of (hRH : RiemannHypothesis) (h : CitedFacts) : OuterStatement
Legendre.squares_of (h : CitedFacts) (c : ComputationClaims) : SquaresStatement
Legendre.main_of (hRH : RiemannHypothesis) (h : CitedFacts) (c : ComputationClaims) : MainStatement
```

`RiemannHypothesis` is Mathlib's proposition; the formal proof of RH uses a later Lean and Mathlib, so it is not imported. `CitedFacts`, in [lean/Legendre/Cited.lean](lean/Legendre/Cited.lean), holds Sorenson–Webster's verification, the theorem of Carneiro, Milinovich and Soundararajan, Davenport's truncated explicit formula, Trudgian's zero count and the Montgomery–Vaughan inequality. `ComputationClaims`, in [lean/Legendre/Claims.lean](lean/Legendre/Claims.lean), holds the two ranges of the 2026 computation that the proof uses.

- **What you trust.** `outer_of` and `main_of` depend on the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and on 5 named checks; `squares_of` on the standard axioms only. Each named check is a Boolean checker written in Lean, with a Lean proof of what a successful run means, and is evaluated with `native_decide`. Each such evaluation adds one compiler-generated axiom stating that the check evaluates to `true`, so you trust the Lean kernel plus the Lean compiler for those evaluations.
- **A correction from the formalisation.** Lemma 14 of the paper needs ae^(−KD) ≥ 2, since the truncated explicit formula holds only for x ≥ 2. The paper now states this; its applications already satisfied it.

To replay, from `lean/`:

```sh
lake build
lake env lean Blueprint.lean
python3 scripts/check_axioms.py
```

A clean CI build took 11 minutes. [lean/REPORT.md](lean/REPORT.md) gives the time of every check, the axiom printout and the comparisons with the programs in `research/`; [lean/BLUEPRINT.md](lean/BLUEPRINT.md) maps the paper's results to Lean declarations. REPORT.md was written in the development repository, so its links to pull requests and CI runs there do not resolve here.

## Citing

BibTeX (also in [CITATION.bib](CITATION.bib) and on the [paper's page](https://charlieoneill11.github.io/maths-releases/legendre/)):

```bibtex
@misc{legendre-2026,
  author       = {O'Neill, Charles and Kirkby, Max and {Astra} and {Fable}},
  title        = {A prime between every two consecutive {$\tfrac{11}{5}$}-th powers},
  year         = {2026},
  month        = nov,
  howpublished = {\url{https://charlieoneill11.github.io/maths-releases/legendre/}},
  note         = {Preprint. Programs and data: \url{https://github.com/charlieoneill11/maths-releases/tree/main/legendre}},
}
```

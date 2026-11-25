# Least prime in every residue class

**Result.** There are absolute constants C, δ > 0 such that, in every sufficiently large dyadic interval, more than 58.7% of the integers n have a prime below C n^(2−δ) in every reduced residue class mod n, simultaneously. The proof does not use the Riemann hypothesis or the generalised Riemann hypothesis.

- Paper: [least-prime-ap.pdf](least-prime-ap.pdf). The LaTeX source is in [paper/](paper/) and builds with `pdflatex main.tex`, run twice.
- Program: [code/verify_split_divisor_density.cpp](code/verify_split_divisor_density.cpp) (SHA-256 `83afd8be…01f131aa`).
- Heuristic cross-check (not used by any proof): [code/pd_window_monte_carlo.c](code/pd_window_monte_carlo.c), a Monte Carlo estimate of the same densities in the Poisson–Dirichlet model.
- Formal proof: [lean/](lean/). Proposition 14 (both numerical bounds) is proved in Lean 4 with Mathlib, and Theorems 1 and 2 from the theorems of Maynard and of Donnelly and Grimmett; see "Formal proof in Lean" below and Section 8 of the paper.

The proof uses Maynard's theorem on primes in all residue classes to large moduli: almost all n with a divisor d in n^0.142858 ≤ d ≤ n^0.199999 have this property. The paper proves two bounds for the limiting proportion of integers with such a divisor, on two different windows:

- more than 58.71% of integers have a divisor in the inward window [n^0.142858, n^0.199999] (lower bound 0.587142);
- fewer than 59.56% have a divisor in the closed window [n^(1/7), n^(1/5)] (upper bound 0.595573, computed on the outward window [0.142857, 0.2], which contains [1/7, 1/5]).

**Prior work.** Tenenbaum proved that the proportion of integers with a divisor in [n^α, n^β] has a limit. Haddad formulated this limit in terms of the Poisson–Dirichlet distribution. Drappeau and Mounier computed it earlier on a grid of windows. Their grid does not contain the two windows above, and the paper does not use their values; Section 5 gives our rigorous bounds on three windows of their grid. A Poisson–Dirichlet Monte Carlo (2·10^7 samples per window) agrees with these bounds, and with Drappeau and Mounier's published enclosure 0.651 ≤ c ≤ 0.666 for their constant c (it gives c ≈ 0.6572).

## Replaying the computation

You need a C++17 compiler.

```sh
cd code
g++ -O3 -std=c++17 verify_split_divisor_density.cpp -o verify
./verify
```

It prints `lower 587142/1000000`, `upper 595573/1000000` and `PASS`. These are the two bounds of the paper's numerical proposition: the lower bound p₆ for the inward window and the upper bound q₅ for the outward window. The program exits with status 0 only if the lower bound is at least 0.587142 and the upper bound at most 0.595573; otherwise it prints `FAIL` and exits with status 1. It takes about 30 seconds on one core of a 2.1 GHz Xeon; it was last run on 24 November 2026.

The heuristic cross-check builds with `gcc -O2 -o pdw pd_window_monte_carlo.c -lm`. `./pdw 20000000 1 0.14 0.20 0.15 0.19 0.15 0.20 0.142857142857143 0.2` prints estimates near 0.6014, 0.5394, 0.5683 and 0.5920, and `./pdw 20000000 2 c` prints c ≈ 0.6572; each takes a few seconds.

## Formal proof in Lean

The folder [lean/](lean/) holds a Lean 4 development, pinned to Lean v4.29.1 and Mathlib v4.29.1. [lean/LeastPrime/Statement.lean](lean/LeastPrime/Statement.lean) states Theorems 1 and 2 and the two bounds of Proposition 14. The bounds `p6_Tin` (0.587142 ≤ p₆(T_in)) and `q5_Tout` (q₅(T_out) ≤ 0.595573) are proved outright. `main_four_of_cited` (Theorem 1 with C = 4), `density_lower_of_cited` and `density_upper_of_cited` (Theorem 2) take `CitedFacts`, in [lean/LeastPrime/Cited.lean](lean/LeastPrime/Cited.lean), whose two fields are Maynard's Corollary 1.4 and the Donnelly–Grimmett theorem. Lean also proves the six bounds of Table 1.

- **What you trust.** Each of the two bounds depends on the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`) and on one named check; Table 1 uses 16 more. Each named check is a Boolean checker written in Lean, with a Lean proof of what a successful run means, and is evaluated with `native_decide`. Each such evaluation adds one compiler-generated axiom stating that the check evaluates to `true`, so you trust the Lean kernel plus the Lean compiler for those evaluations.

To replay, from `lean/`:

```sh
lake build
lake env lean Blueprint.lean
python3 scripts/check_axioms.py
```

A clean CI build took 27 minutes. [lean/REPORT.md](lean/REPORT.md) gives the time of every check, the axiom printout and the comparison with the C++ program; [lean/BLUEPRINT.md](lean/BLUEPRINT.md) maps the paper's results to Lean declarations. REPORT.md was written in the development repository, so its links to pull requests and CI runs there do not resolve here.

## Citing

BibTeX (also in [CITATION.bib](CITATION.bib) and on the [paper's page](https://charlieoneill11.github.io/maths-releases/least-prime-ap/)):

```bibtex
@misc{least-prime-ap-2026,
  author       = {O'Neill, Charles and Kirkby, Max and {Astra} and {Fable}},
  title        = {Primes below {$n^{2-\delta}$} in every residue class, for a majority of moduli},
  year         = {2026},
  month        = nov,
  howpublished = {\url{https://charlieoneill11.github.io/maths-releases/least-prime-ap/}},
  note         = {Preprint. Programs and data: \url{https://github.com/charlieoneill11/maths-releases/tree/main/least-prime-ap}},
}
```

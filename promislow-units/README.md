# The unit conjecture fails for integral group rings

**Result.** The integral group ring ℤ[P] of the Promislow group P = ⟨a, b | b⁻¹a²b = a⁻², a⁻¹b²a = b⁻²⟩ has a non-trivial unit: there are u, v ∈ ℤ[P] with uv = vu = 1 and u ≠ ±g for every g ∈ P. Since P is torsion-free, this answers Higman's 1940 question over the integers in the negative, and the unit conjecture fails over ℚ and ℝ, where it was still open. Gardam had found non-trivial units of P over 𝔽₂ and over ℂ (with coefficients in ℤ[ζ₈]), and Murray over every 𝔽ₚ. The reduction of u modulo every prime is again a non-trivial unit, so one integral unit covers every field. The paper also gives a non-trivial unit of ℤ[P] that is congruent to 1 modulo 2.

- Paper: [promislow-units.pdf](promislow-units.pdf). The LaTeX source is in [paper/](paper/) and builds with `pdflatex main.tex`, run twice.
- Certificate and programs: [code/](code/).
- Formal proof: [lean/](lean/). Lean 4 with Mathlib proves that ℤ[P] has a non-trivial unit, including the integrality of u and v, and the unit congruent to 1 modulo 2; see "Formal proof in Lean" below and the paper's section "Formal verification in Lean".

## The unit

Write x = a², y = b², z = (ab)². For the three letter types (vertex, m, k) = (a, 3, 3), (a, 5, 3) and (b, 3, 15), the paper (Section 3) defines units A₁, A₂ and B of the localisation of ℤ[P] at the central elements F₁ = x⁻¹ + 1 + x, F₂ = x⁻² + x⁻¹ + 1 + x + x² and F₃ = y⁻¹ + 1 + y. Each is a product of eight elements P_m(t) + Q_m(t)·c·h divided by F⁴. With [X, Y] = XYX⁻¹Y⁻¹,

  u = [[[W₁, W₂], W₁], W₁],  W₁ = [A₁, B],  W₂ = [A₂, B],

and v is the formal inverse of this word, so uv = vu = 1 holds automatically in the localisation. The paper's Theorem 6 proves that u and v have integer coefficients. It works one prime at a time: after conjugation by half of the letter belonging to that prime, each W_i is congruent to 1 modulo the prime, and each commutator gains a power. Non-triviality follows from two coefficients of u: x⁻¹⁴²⁰y⁻²⁰⁸z¹⁴a has coefficient 3⁷ = 2187 and x¹⁴¹⁹y²⁰²z¹⁴a has −3⁷.

[code/integral-pair.json](code/integral-pair.json) is the certificate. It lists the three letter types, the eight phases (sign and exponent of v₀ = w^k) and the two freely reduced words for u and v, each with 64 letters (1, 2, 3 for A₁, A₂, B and negative for inverses). The common denominator of both words is D = F₁⁸⁰F₂⁶⁴F₃¹¹². The integer coefficients can be read off by a finite formula: with M = 20000, H_x = Φ₃(x)⁸⁰Φ₅(x)⁶⁴ and H_y = Φ₃(y)¹¹², let K_H be the power series of 1/H truncated at degree 2M. The coefficients of u (or v) are the terms with −M ≤ i, j ≤ M, in the normal form xⁱyʲzᵏr, of K_{H_x}(x)K_{H_y}(y)x²⁰⁸y¹¹² times the product of the 64 integer letter numerators.

## Checking the result

From `code/`, with Python 3.10 or newer and [python-flint](https://pypi.org/project/python-flint/) 0.9:

```sh
python3 check_unit.py integral-pair.json   # independent check (written from the paper's definitions)
python3 integral_unit.py                   # letter identities, both cleared products, extreme coefficients
python3 joint_midpoint_check.py            # the twelve congruences of the paper's Lemma 9, by polynomial division
python3 integral_unit_images.py            # exact rational images, and reductions modulo 2, 4 and 8
python3 integer_coefficient.py             # any single coefficient by the finite formula above
python3 verify.py                          # replays the earlier units over F_2, F_3 and Z[zeta_8] in the same model
```

Each takes at most a few seconds. `integral_unit.py` and `integer_coefficient.py` need only the standard library; `integer_coefficient.py --word u --site -1420 -208 14 1` prints the coefficient 2187.

`check_unit.py` shares no code with the other programs. It proves the identities of the paper's Lemmas 3 and 4 by exact expansion of the six signed letters. It then reduces the coefficient polynomials of the integer numerators of u and v modulo F₁⁸⁰, F₂⁶⁴ and F₃¹¹², with the two remaining variables set to random residues modulo two primes near 2⁶¹ and 2⁶², and finds that they vanish, and that one more power of each prime does not divide them. A word with one letter inverted fails the test. Because it evaluates at random points, this is a confirmation of Theorem 6, not a proof; the proof is the argument in the paper. The program also checks both products at a random point and computes the values used in the paper's Proposition 10, Corollary 2 and Proposition 11.

`verify.py` provides the affine model of P used by three of the other programs (a acts on ℝ³ by diag(1, −1, −1) plus (1, 1, 0), b by diag(−1, 1, −1) plus (0, 1, 1)). Run on its own, it checks this model against a list of 52 supports in [code/census52.txt](code/census52.txt) and replays Gardam's unit over 𝔽₂, Murray's over 𝔽₃ and Gardam's over ℤ[ζ₈], using [code/examples.py](code/examples.py) and [code/ring.py](code/ring.py).

## Formal proof in Lean

The folder [lean/](lean/) holds a Lean 4 development of about 2,100 lines in 21 modules. Its main theorem, `Promislow.recorded_certificate` in [lean/Promislow.lean](lean/Promislow.lean), gives u, v in mathlib's `MonoidAlgebra ℤ ElemP` with uv = vu = 1, with D·u and D·v equal to the cleared numerators of the two words in [code/integral-pair.json](code/integral-pair.json), and with u ≠ ±g for every g. The certificate is read during the build, and Lean checks that its words, letter types, phases and denominator powers agree with the definitions. The development also proves:

- `torsionFree`, and `Presentation.equiv`, which identifies the normal-form model with the two-relator presentation above;
- `presented_nontrivial_integral_unit`: the same result for the presented group;
- `nontrivial_reduction_certificate`: the reduction of u modulo 2 is not a group element;
- `identity_reduction_certificate`: the unit of the paper's Proposition 11, which reduces to 1 modulo 2 and is non-trivial;
- `integral_conjecture_false`: it is false that every unit of the integral group ring of every torsion-free group is ±g.

The integrality proof follows Section 4 of the paper. In place of unique factorisation it uses the identity (F₁ − 1)F₁ − F₂ = 1 and a recurrence along the powers of y. Non-triviality uses the representation of the paper's Proposition 10(b) over 𝔽₁₇ and a permutation representation of degree 28 over 𝔽₂. The coefficients ±2187 are not in Lean.

- **Pins.** Lean v4.24.0 and Mathlib v4.24.0, pinned in `lean-toolchain` and `lake-manifest.json`.
- **What you trust.** [lean/Audit.lean](lean/Audit.lean) prints the axioms of the main theorems. Torsion-freeness depends only on the three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The unit theorems also depend on `Lean.ofReduceBool` and `Lean.trustCompiler`, because the finite computations (the letter identities, the divisibilities, the two matrix images and the image modulo 2) are evaluated with `native_decide`. There is no `sorry` and no project axiom. So you trust the Lean kernel and, for those evaluations, the Lean compiler.
- **Credit.** The group operations and the proof of torsion-freeness are adapted from Alexander S. Donahue's Apache-2.0 development ([lean/LICENSE-Donahue](lean/LICENSE-Donahue)).

To replay, from `lean/`:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

[lean/README.md](lean/README.md) walks through the proof module by module.

The development was copied from `promislow-units/lean/` at commit e8b9202 of the development repository. The two paths to the certificate were changed from `../integral-pair.json` to `../code/integral-pair.json` to match the layout of this folder.

## Citing

```bibtex
@misc{promislow-units-2026,
  author       = {O'Neill, Charles and {Astra}},
  title        = {The unit conjecture fails for integral group rings},
  year         = {2026},
  month        = nov,
  howpublished = {\url{https://charlesponeill.com/maths-releases/promislow-units/}},
  note         = {Preprint. Programs and data: \url{https://github.com/charlieoneill11/maths-releases/tree/main/promislow-units}},
}
```

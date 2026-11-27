# Lean proof of a nontrivial integral Promislow unit

The theorem `Promislow.recorded_certificate` gives two elements of mathlib's `MonoidAlgebra ℤ ElemP`. Their coefficients have finite support by definition. Their products in both orders are one, and the first element differs from both signs of every basis element. Each element satisfies the cleared numerator equation for its own signed word in [the certificate](../code/integral-pair.json). The denominator is a product of regular central factors, so the equations specify the elements uniquely. [Theorem statements](Promislow.lean)

| Declaration | Statement |
|---|---|
| `Promislow.torsionFree` | For every group element and every positive natural power, if the power is one then the element is one. |
| `Promislow.Presentation.equiv` | The abstract group with relators `a⁻¹ b² a b²` and `b⁻¹ a² b a²` is isomorphic to the coordinate group. |
| `Promislow.presented_nontrivial_integral_unit` | The integral group ring of that two-relator quotient contains a nontrivial unit. |
| `Promislow.nontrivial_integral_unit` | The unit group of the integral group ring contains an element outside all signed basis elements. |
| `Promislow.nontrivial_reduction_certificate` | The first integral unit remains distinct from every basis element after reducing coefficients modulo two. |
| `Promislow.identity_reduction_certificate` | A second nontrivial two-sided integral unit reduces to one in the mod-2 group ring. |
| `Promislow.integral_conjecture_false` | The assertion that every integral unit of every torsion-free group is a signed group element is false. |

## Replay

From the root of this repository, use an installation of elan with the pinned Lean 4.24.0 toolchain. The manifest pins mathlib at `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

```sh
cd promislow-units/lean
lake exe cache get
lake build
lake env lean Audit.lean
```

Lake tracks the certificate `../code/integral-pair.json` as a build input. The elaborator reads both words, the vertices, the phases and the stated denominator powers. Lean checks their agreement with the definitions, including free reduction, multiplicities and the order of the inverse. [Artifact reader](Promislow/Recorded.lean)

## Proof and trust

The group model uses the left normal form `x^i y^j z^k c`, with `x = a²`, `y = b²`, `z = (ab)²` and four choices of `c`. The cocycle is Gardam's multiplication table. The Lean group operations and torsion-freeness proof adapt Alexander S. Donahue's Apache-2.0 development at commit `8b7164514b692747ee62c051b32b0765202f848c`. [Gardam's paper](https://arxiv.org/abs/2102.11818v3) · [Donahue's source](https://github.com/0thernes/promislow-fracton-amoeba/blob/8b7164514b692747ee62c051b32b0765202f848c/lean/PromislowFracton/PromislowGroup.lean) · [License](LICENSE-Donahue)

The presentation isomorphism collects words inside mathlib’s quotient of the free group. The evaluation of a normal form and the coordinate map are proved inverse in both directions. [Presentation proof](Promislow/Presentation.lean)

1. The sparse integer operations have a proved interpretation in the group ring. They verify the two-sided numerator identities and the factor divisibilities for the three vertex units. [Sparse arithmetic](Promislow/Sparse.lean) · [Letter identities](Promislow/Letters.lean) · [Divisibility](Promislow/Contact.lean)
2. In an injective central localization, the nested commutators gain four powers of each possible denominator. A recurrence on finite Laurent slices and a Bézout identity combine the three divisibility results. This proves integrality of the element and its inverse before either inverse equation is transported back. [Localization](Promislow/Localization.lean) · [Combining the factors](Promislow/Gluing.lean) · [Integrality](Promislow/Integrality.lean)
3. A ring homomorphism to four-by-four matrices over `ZMod 17` sends each signed group element to a monomial matrix. The first row of the unit is `(11,16,1,12)` in the row-action convention here. Twisting its inverse by the sign character of the second translation coordinate gives a second witness with first two entries `(12,8)` and identity reduction modulo two. [Representation](Promislow/Image.lean) · [Sign twist](Promislow/Sign.lean)

4. A separate right action on the four cosets times seven translation residues detects the first unit after coefficient reduction modulo two. The denominator fixes a chosen basis vector, while the numerator sends it to a vector with nonzero entries in two cosets. [Binary reduction](Promislow/Binary.lean)

The axiom audit reports `propext`, `Classical.choice` and `Quot.sound` for torsion-freeness. For the unit theorems it also reports `Lean.ofReduceBool` and `Lean.trustCompiler` because the finite sparse arithmetic and matrix evaluations use Lean 4.24's `native_decide`. The project has no proof placeholders or project-specific axioms. The two exact coefficients of magnitude 2187 in the hand proof have a separate [Python coefficient replay](../code/integer_coefficient.py).

# Independent scalar multipliers on K and the field

Let K = ℤ₇ × ℤ₁₉ and let G = K × (𝔽₉,+). Suppose each of the four odd Spence sign blocks is invariant under K₀ × F₀. Here K₀ is a subgroup of ℤ₇* × ℤ₁₉*, and F₀ either multiplies by the four nonzero field squares or flips the two coordinates of 𝔽₃² independently.

**All 24 choices of K₀ with at most 16 orbits on K are excluded for both choices of F₀.** There are 50 scalar subgroups on K in total. The 24 in question have 16 inclusion-minimal members. Each larger member contains a minimal member, so its invariant blocks would also solve a case tested below. The proposed generators (2,4) and (2,5) each have 17 orbits.

## Exact screens

Normalize every block to total +1. For a quotient with kernel size k, its four compressed autocorrelations must sum to 4792−4k at zero and −4k elsewhere. If a subgroup of order t acts independently on a prime factor of order p, every compressed entry after summing out that factor is a signed sum of 1 and (p−1)/t copies of t. Write m for the least possible magnitude. The zero-shift equation gives

    4(1197/p)m² ≤ 4792−4p.

For example, an independent order-six subgroup on the 19-coordinate has m = 5. The left side is 6300 and the required energy is 4716. This removes its entire family for either field action.

For a transitive prime projection, each compressed field sheet has value a at zero and a common value b elsewhere. Its nontrivial Fourier value is a−b. Four squared values must sum to 4792 at every nontrivial character, including those mixing the prime and field axes. The program enumerates the exact attainable sheet sums and follows them through these equations. For the quadratic-residue projection on p = 7 or 19, the corresponding squared norm of a triple (a,b,c) is ((2a−b−c)²+p(b−c)²)/4. The finite join on the transitive cases packs each vector of nonnegative powers in base 32768, larger than four times the single-block bound. This encoding has no carries or collisions.

For independent quadratic-residue multipliers on both prime axes, the complex Fourier values at a mixed prime character lie in ℚ(√−7,√−19). With the field character applied first, write 4F = A + B√−7 + C√−19 − D√133. Its squared modulus times 16 is

    A² + 7B² + 19C² + 133D² + 2(BC−AD)√133.

Equality is tested on both integer coordinates. For each field channel there are also the trivial power and the two single-prime powers. In the field-squares case, 2,848 bounded rows give 2,711 distinct full spectra. In the coordinate-flip case, 250,368 rows give 248,091. Both four-block joins have zero fingerprints with the required sum.

The remaining mixed case has the sign flip on ℤ₇ and the order-nine squares on ℤ₁₉. For field squares, enumerate the twelve K-orbit signs of each sheet. An integral Gaussian test vector w bounds a block convolution C by |w* C w|² ≤ 4792 (w* w)². Rounded character samples only select the vector. Subsequent products and comparisons use integers. The four-block join uses the literal integer PAF at every representative shift. The run retained 244,638 bounded rows and found zero matching fingerprints. With coordinate flips on the field, already the full ℤ₇ × 𝔽₃² compression is empty. At each of its four prime cosets, an untransformed sheet value belongs to {±1,±17,±19}. The origin-energy constraints leave 464 site vectors at zero and 176 at each other coset. There are 19,756,671 row-sum-one choices, of which 70,402 survive energy and integer character bounds. None of the 40,595,632 checked pair entries yields a matching fingerprint.

The group enumeration closes subgroups explicitly under multiplication. Character and lag representatives are obtained from the resulting point orbits. An equality of full integer spectra implies equality of their additive 64-bit fingerprints. In these negative joins the number of complementary fingerprints is zero. The sign files written on a positive full Spence result are checked at every original shift before output.

## Reproduction

Use a fresh work directory with a C++17 compiler, Python 3 and NumPy. From this folder run

```sh
python3 audit_shapes.py /tmp/hadamard-scalar-audit
```

The driver rebuilds its native checkers, regenerates the scalar subgroups, tests all inclusion-minimal cases, and writes `shape-results.json` with the generating units, orbit counts, and separate results for both field actions. The [order-4792 construction](README.md) uses the order-36 group with K generator (2,4). This enumeration concerns the larger scalar actions specified above.

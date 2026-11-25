# Hadwiger–Nelson verification report

## Statement review

Lean proved that every list of at most **245,510 unit segments** in the Euclidean plane admits a proper six-colouring. It also proved that every set of **10,689 or fewer points** admits a six-colouring that separates every unit-distance pair, assuming the four drawing facts stated below. The unconditional target `points_le_10689` is recorded as a proposition. The complete proofs are `edges_le_245510` and `points_le_10689_of_cited`. [Public statements](HadwigerNelson/Statement.lean) · [Proofs](HadwigerNelson/Proof/Bounds.lean)

Charlie approved the public statements and cited hypotheses on 24 November 2026. Their Git blobs are `a3072dffa1528c95c78d84e5224a73195c562ad4` and `fa5981c174be747ce665f6461a01f3537d9a9ceb`. The paper's programs provide untrusted numerical comparisons. Every numerical fact used by either public theorem is checked in Lean.

Lean and Mathlib use v4.29.1. The pinned Mathlib commit is `5e932f97dd25535344f80f9dd8da3aab83df0fe6`. The report follows the release at `7541cf08200934aecee19c1551539f06d4af723e`. [Release source](https://github.com/charlieoneill11/maths-releases/blob/7541cf08200934aecee19c1551539f06d4af723e/hadwiger-nelson/paper/main.tex)

## Cited hypotheses for the point theorem

Vertex and edge labels are finite. The endpoints of an edge are ordered by vertex label. Distinct labels may have the same endpoints in a multigraph. A simple graph has no such duplicates. Raw drawings use continuous injective arcs. The crossing count records each unordered edge pair and each common interior point, including contacts and multiple crossings. A good drawing has only proper crossings, defined by a local homeomorphism to two coordinate axes, and no triple crossings. Its distinct edges meet at most once, and adjacent edges have disjoint interiors. These conventions make the five-planar density theorem apply to exactly the kind of drawing it requires. The comparison with a raw drawing is used for the simple subgraphs obtained in the halving argument.

```lean
structure CitedFacts : Prop where
  /-- Büngener–Kaufmann, JGAA 29 (2025), Theorem 4(b), equivalently
  arXiv:2409.01733v2, Theorem 6(b). The inequality is multiplied by nine. -/
  crossing_lower : ∀ {n m} (G : Graph n m), G.IsSimple → 3 ≤ n →
    45 * (m : ℤ) - 203 * ((n : ℤ) - 2) ≤ 9 * (crossingNumber G : ℤ)
  /-- Büngener–Franz–Kaufmann–Pfister, GD 2026, Theorem 7.
  A simple 5-planar graph has at most 7(n − 2) edges. -/
  five_planar : ∀ {n m} (G : Graph n m), G.IsSimple → 3 ≤ n →
    ∀ D : Drawing G, D.IsGood → (∀ e, D.crossingsOn e ≤ 5) → m ≤ 7 * (n - 2)
  /-- Schaefer, DS21, “What is a drawing?” and “The crossing number”.
  Perturbing arbitrary drawings into general position gives this comparison
  when each pair of edges has finitely many common points (paper §5). -/
  le_drawing : ∀ {n m} (G : Graph n m), G.IsSimple → ∀ D : Drawing G,
    D.FiniteIntersections → crossingNumber G ≤ D.crossingCount
  /-- Schaefer, DS21, “The crossing number”. A simple graph has a good drawing
  attaining its ordinary crossing number, including graphs with isolated vertices. -/
  attained : ∀ {n m} (G : Graph n m), G.IsSimple →
    ∃ D : Drawing G, D.IsGood ∧ D.crossingCount = crossingNumber G
```

The two numbered results are Theorem 4(b) of the published Büngener–Kaufmann paper and Theorem 7 of the GD proceedings paper. The two drawing properties are from Schaefer’s survey, especially §2.2.1. The hypotheses are explicit arguments to the point theorem. [Büngener–Kaufmann](https://doi.org/10.7155/jgaa.v29i3.3000) · [Büngener–Franz–Kaufmann–Pfister](https://doi.org/10.4230/LIPIcs.GD.2026.33) · [Schaefer](https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS21)

## Numerical cross-checks

### Complete wave and edge thresholds

The paper gives `p_E = 2038573446989 / 500000000000000000`. The certified integer-bin proof uses the weaker target `B = 4077152 / 10¹²` for the two stated edge counts. Exact rational multiplication gives `245269 B = 0.999998993888` and `245510 (B − 4 / 10⁹) = 0.99999954752`. The second inequality also requires the paper's star improvement. The quoted trial at 2²⁸ bins is larger than the paper's exact Theorem 3 constant. Lean has proved the real probability bound, both threshold multiplications, and the 245,269-edge theorem.

Running the release's unchanged `cap14_global_angle.cpp` at 2²⁰ bins on `cap22_finite_edge_profile.json` produced the integer sum `2958963959923292564`. Normalising it by `2/(923677693607 · 500000000000 · πlow)`, with `πlow = 314159265358979323846/10²⁰`, gives **4.078771146359895 × 10⁻⁶**. This differs from the prompt's trial value of **4.0782 × 10⁻⁶**. An independent integration of the piecewise-linear complete-wave profile gave 4.07877114634219 × 10⁻⁶, and eight exact individual-bin checks agreed with the reference code. These are program comparisons. The release's Theorem 3 uses a different quadrature.

At 2²⁴ bins the release checker produced `2957858138797887094` in 23.55 user CPU seconds. Its upper bound of 4.077246831984854 × 10⁻⁶ agrees with the prompt’s 4.07725 × 10⁻⁶ at the quoted precision.

At 2²⁸ bins the release checker produced `2957789034267010495`, giving the exact upper bound `591557806853402099000000000/145090952826025756378836808426261`. Its decimal value, 4.077151575141432 × 10⁻⁶, agrees with the prompt's 4.0771516 × 10⁻⁶ to the quoted precision. The run used 383.633 CPU seconds and 1,330.583 elapsed seconds on a low-priority core shared with the Lean build. The independently compiled Lean checker matched the C++ total exactly at both resolutions. At 2²⁰ bins it used 1.24 CPU seconds. At 2²⁸ bins it used 303.378 CPU seconds, 831.374 seconds elapsed, and 9 MiB peak resident memory. Only six of the 32 contiguous groups had nonzero sums. These are execution times for the feasibility trial. The six official proof timings are listed below.

Lean checked that 26 of the 32 angular groups have zero contribution, using two disjoint angle ranges and a kernel-checked maximum ordinate. Six certified native evaluations cover the remaining groups. The fixed complete-wave right profile is globally 1-Lipschitz, including across period boundaries. The literal profile and the placement law now prove that every fixed vertex almost surely receives a colour.

### Certified 245,269-edge milestone

The unconditional theorem `edges_le_245269` follows from `Wave.complete_monoProb_upper` and `Proof.edges_of_union_bound`. For any specified unit edge the random placement has monochromatic probability at most 4,077,152 / 10¹². For 245,269 edges the expected number of conflicts is at most 0.999998993888, so some placement avoids them all. The complete wave assigns a colour almost surely to every endpoint. The proof also covers repeated endpoints and a list containing both orientations of a segment. [Proof](HadwigerNelson/Blueprint/Milestone.lean)

The six native declarations have names `HadwigerNelson.Angular.Native.blockNNN`. Each proves the executable Boolean check for the corresponding 2²³ angular bins. The real soundness theorem `Angular.checkGroup_integral_bound` bounds the integral of the two physical overlap contributions over those bins. `Angular.complete_probability_of_sum` assembles these group bounds using the placement law. Each soundness theorem uses the three standard axioms. Lean printed those same three for `edges_le_245269` together with exactly `HadwigerNelson.Angular.Native.blockNNN._native.native_decide.ax_1_1` for the six rows below. The per-declaration allowlist and Boolean goal-type checks passed.

| Certificate file under HadwigerNelson/Native | Lake module seconds | Total target CPU seconds |
| --- | ---: | ---: |
| Angular/Block003.lean | 10 | 12.17 |
| Angular/Block004.lean | 66 | 67.53 |
| Angular/Block005.lean | 67 | 67.69 |
| Angular/Block006.lean | 84 | 72.95 |
| Angular/Block007.lean | 66 | 68.01 |
| Angular/Block008.lean | 36 | 38.86 |

### Complete-wave star certificate

An integer-only pilot used a Gaussian fixed-point denominator of 2⁸⁰ and the rational lower and upper bounds 2(η − η³/3) and 2η for each angular increment. It covered 14,464 Fourier rectangles and 252 native rectangles in 227.0 elapsed seconds. The independently compiled Lean star checker also passed every degree case in 223 seconds of user CPU time. The Fejér slack is the required lower bound minus the certified weighted threshold sum.

| Degree case | Measured slack |
| --- | ---: |
| Up to 23, evaluated at 23 | 798769232681 / 6555000000000 |
| 24 | 200424269 / 19000000000 |
| 25 | 32141578553 / 142500000000 |
| 26 | 2339108277437 / 3705000000000 |
| 27 | 878874413663 / 855000000000 |
| 28 and above, excess native credit at 28 over 8 × 10⁻⁹ | 185444988259 / 57729855850437500000 |

Lean has checked the degree-independent Fejér power-sum inequality (Lemma 22) and the threshold implication (Lemma 24) using only the three standard axioms. Lean also checked that the five finite degree tests imply the claimed bound for every positive degree, provided the box estimates hold for the actual angular gain. Lean checked the classifier enclosures for the actual colour responses, their integrals, and the sum over the twelve physical copies. For each physical source, `row_magnitude_lower` certifies the normalized Fourier magnitude after integer square-root rounding, truncation of the Gaussian operations and the error allowance for undecided arc spans. The real soundness theorem `Stars.BoxCheck.complete_gain_of_check` proves an expected gain of at least (8 / 10⁹) times the degree at every specified vertex from the two Boolean checks. Its real proof has only the three standard axioms.

For 105 sampled Fourier rectangles across the three complete-wave families, the Lean integers at scale 2⁸⁰ agree with the release’s 100-bit ball-arithmetic code in every rounded mean and all 5,880 rounded Fourier magnitudes at quantum 10⁻¹⁰. Eight sampled native fractions agree as well. Before the 10⁻¹⁰ floor, the largest sampled difference between the release’s lower estimate and the fixed-point lower estimate was approximately 4.07341 × 10⁻¹³ for a mean and 1.39921 × 10⁻¹⁴ for a Fourier magnitude. For rectangle zero, the integer values for the mean and harmonics 1 and 56 are −2215039, 108261298 and 48905895. The samples include the rectangle indices divisible by 151 below 14,464 and the family boundaries.

The separately certified layout covers the physical containment and pairwise separation of the boxes used for each degree. The source checker compares the fixed rectangles with the actual half-tile bounds. A stock-kernel trial for source row 7,783 reached 2,831,292 KiB of private memory in 15.07 CPU seconds before termination. The same import alone used 136,384 KiB. [Layout soundness](HadwigerNelson/Stars/LayoutSound.lean)

| Certificate file under HadwigerNelson/Native | Native declaration | Real soundness | Tactic seconds | Lake module seconds |
| --- | --- | --- | ---: | ---: |
| Stars/Layout.lean | `Stars.BoxCheck.sourceBoxes_checked` | `Stars.BoxCheck.checkSourceBoxes_physical` gives containment and separation of both families | 0.543222 | 3.0 |

| Certificate file under HadwigerNelson/Native | Native declaration | Real soundness | Lake module seconds | Total target CPU seconds |
| --- | --- | --- | ---: | ---: |
| Stars/Complete.lean | `Stars.BoxCheck.complete_checked` | `Stars.BoxCheck.complete_gain_of_check` bounds the gain at each physical vertex from the credit and layout checks | 127 | 117.29 |

### Unconditional 245,510-edge theorem

The §4 proof applies the one-bad-edge recolouring argument to the physical wave. Summing the star credit over actual incidences gives the strict bound `245510 · (4077152/10¹² − 4/10⁹) = 0.99999954752 < 1`. The term for the partial-wave point theorem is absent from the edge theorem's axiom dependencies. [Edge proof](HadwigerNelson/Blueprint/Edge.lean) · [Soundness of the star check](HadwigerNelson/Stars/CompleteSound.lean)

### Pointwise packing in place of the planar estimates

Using the pointwise neighbour-count bound of Lemma 31 in both collision parameters removes the need for the planar and 1-planar density estimates in Lemma 32. We tested this change before selecting the cited hypotheses. From the pinned release’s `hadwiger-nelson/code/` directory, the following Python fragment recomputes the parameters and feeds the changed values directly to both reference box checkers.

```python
import json
from pathlib import Path
import cap15_finite_nested as nested
import cap22_point_parameters as parameters
import cap22_point_combined as combined
import cap22_point_crosscheck as crosscheck

nested.area_count = lambda ratio: 0  # credits then uses the pointwise bound
g = parameters.geometry()
receipt = json.loads(Path('cap22_partial_star_result.json').read_text())
star = receipt['per_incidence_excess_picounits'] * (combined.SCALE // 10**12)
print(combined.Bounds(10689, g, star).check())
print(crosscheck.audit(10689, g, star))
```

| Quantity | Paper/release | Pointwise variant | Comparison |
| --- | ---: | ---: | --- |
| Scaled L | 142407225756 | 150296106235 | Higher |
| Scaled T | 95763744940 | 97911102803 | Higher |
| Edge ceiling | 403078 | 403078 | Equal |
| Primary boxes examined | 66601 | 66601 | Equal |
| Primary maximum in units of 10⁻¹⁸ | 999999995095531514 | 999999995095531514 | Equal |
| Second checker boxes examined | 46865 | 46867 | Two more |

The two reference implementations share routines for centre credit and close-pair counts. The 19.51 s pilot established feasibility at 10,689. Lean now proves the pointwise packing and close-pair bounds, the crossing-number improvement, sampling and halving, the cyclic unit-arc drawing, the degree variance and the 403,078-edge ceiling. Their axiom audits contain only the three standard axioms. The rational packing routine agreed with the release on all 16,384 bin caps (sum 190,582, maximum 41).

The verified Proposition 53 checker uses rational interval arithmetic on the displayed objective. A single set of formulas is interpreted over both the reals and intervals, with directed integer square roots. The Lean proof identifies the real interpretation with both paper profiles, their seven angular budget terms, and the three forest expressions. It checks every feasible integer triple, including the nonmonotone variance expression. With the pointwise packing constants, this evaluator visited **66,737** boxes. It encloses intermediate variables independently, whereas the release's **66,601**-box traversal uses additional monotonicity and integer rounding. Both accepted the entire simplex at 10,689. The Lean traversal accepted all 33,369 leaves. Its unique largest rational leaf upper bound was 43137749977189051651204680125639 / 43137750000000000000000000000000. Its upward rounding to units of 10⁻¹⁸ is **999999999471206812**, 4,375,675,298 units higher than the release’s maximum. That leaf covers `m = 400620…400717`, `s = 153…157`, `j = 32…41`. The strict bound below one holds throughout the leaf. [Executable checker](HadwigerNelson/Certificate/BoxSearch.lean) · [Real soundness](HadwigerNelson/Certificate/PointBoxes.lean)

| Certificate file under HadwigerNelson/Native | Native declaration | Soundness | Lake module seconds |
| --- | --- | --- | ---: |
| Point/Boxes.lean | `Certificate.ParameterBoxes.boxes_checked` | `Certificate.point_bound_of_check` proves the real objective is strictly below one at every feasible triple | 111 |
| PartialLayout/SourceBoxes.lean | `Stars.PartialCheck.Layout.checked` | `Stars.PartialCheck.Layout.check_physical` establishes containment and disjointness for the 136,743 partial-wave source rectangles | 32.16 total wall, 11.80 CPU |

The axiom report for `Certificate.point_bound_lt_one` contains the standard three and exactly `HadwigerNelson.Certificate.ParameterBoxes.boxes_checked._native.native_decide.ax_1_1`. Proposition 44 supplies the opposite inequality for the objective of a hypothetical counterexample.

### Partial-wave geometry and numerical constants

Lean proved the continuous hole covariogram formula and coordinatewise monotonicity, the two lattice alignments for simultaneous blanks, and the rounded positive-chord enclosure. The executable mesh clips 68 alternating original and shifted knot intervals. Its soundness proof verifies the physical left wall on both sides of zero, the exact rounded interpolation at every breakpoint and the integration of every clipped slab. The two verified numerical sweeps reproduced B = 112668096940, C = 16034576942481, E = 3057937052494 and the two retention fractions 344 and 761 per thousand. Its two caps were exactly 1206695810097/46155578012300000 and 1670178375963/230777890061500000. [Hole soundness](HadwigerNelson/Certificate/Hole/Physical.lean)

Two Boolean checks and their real soundness theorems give all nine inequalities in `Certificate.partialConstants`. Lean and the reference code agree on the seven scaled values for B, C, E, L, T, U and J. The last four use the pointwise packing variant in the table above. In units of 10⁻¹⁸, U is 104770006866 and J is 300592212470. The weighted short-edge sums use a downward rounding to multiples of 10⁻³² per bin. The proof bounds the error in the required direction. [Mean estimates](HadwigerNelson/Certificate/Hole/TableSound.lean) · [Packing estimates](HadwigerNelson/Certificate/Hole/PackingBounds.lean)

| Certificate file under HadwigerNelson/Native | Native declaration | Real interpretation | Lake module seconds | Total CPU seconds |
| --- | --- | --- | ---: | ---: |
| Point/Means.lean | `Certificate.Hole.means_checked` | `Hole.checkMeans_sound` proves three mean lower bounds and both retained fractions | 70 | 37.10 |
| Point/Packing.lean | `Certificate.Hole.packing_checked` | `Hole.checkPacking_sound` bounds four collision losses with a certified neighbour cap in each angular bin | 32 | 18.72 |

The partial angular check at 2²⁶ bins gives the same integer total as the release C++, 513912833598490555. Lean bounds the real probability by 102782566719698111 / 145001902327661557000000. The blank density from the integral of the actual left profile is 82102466727 / 1153889450307500. Both fractions agree exactly with the paper. Rounding upward to multiples of 10⁻¹⁸ gives 71152801254159 for the blank density and 708385488148 for the probability after subtracting half the star credit, also equal to the release.

| Certificate file under HadwigerNelson/Native | Declaration under Angular.Partial.Native | Total elapsed seconds | Total CPU seconds |
| --- | --- | ---: | ---: |
| PartialAngular/Block003.lean | `block003` | 98.30 | 50.20 |
| PartialAngular/Block004.lean | `block004` | 375.36 | 167.11 |
| PartialAngular/Block005.lean | `block005` | 86.67 | 35.48 |
| PartialAngular/Block006.lean | `block006` | 450.10 | 204.76 |
| PartialAngular/Block007.lean | `block007` | 221.47 | 118.56 |
| PartialAngular/Block008.lean | `block008` | 159.84 | 86.35 |

Each of the six checks bounds a contiguous group of 2²¹ angular bins. `Angular.Partial.probability_of_groups` turns the group sums into a bound for the actual overlap probability. The kernel proves the other 26 groups contribute zero. The integer group sums for 003 through 008 are 36866779966835711, 70791220128326594, 886673243597054, 67417806072575198, 0 and 337950354187155998. They match the independently compiled release implementation group by group. [Angular checker](HadwigerNelson/Angular/Partial/Checked.lean)

Lean proved the translation and rotation inequalities for the physical centre event. Six small-chord interval checks give lower bounds that exceed their respective intercepts. In units of 10⁻¹⁸, the release gives 23255589905 and 7998615681 for the coarse profile and 25974340509 and 9302887730 for the fine profile. The minimum medium-chord margins in the release are 174440621 and 40580629, over 61 intervals for each profile. [Small-chord proof](HadwigerNelson/Centres/Events/Small.lean) · [Medium-chord proof](HadwigerNelson/Centres/Events/Medium.lean)

| Certificate file under HadwigerNelson/Native | Declaration under Centres.Quadrature.Native | Real soundness | Total elapsed seconds | Total CPU seconds |
| --- | --- | --- | ---: | ---: |
| Centres/Small.lean | `smallIntervals` | `smallPass_real` gives lower bounds on the actual small-chord rectangle widths | 14.05 | 7.84 |
| Centres/MediumCoarse.lean | `mediumCoarse` | `mediumPass_real` bounds the coarse-profile overlap | 39.20 | 13.39 |
| Centres/MediumFine.lean | `mediumFine` | `mediumPass_real` bounds the fine-profile overlap | 56.17 | 20.53 |

For the partial-wave star, the fixed-point Gaussian recurrence uses denominator 10¹². The signed and native families contain 132,621 and 4,122 source rectangles. The threshold witnesses for all 88 finite degrees give 9,121 frequency and threshold pairs, of which 3,171 are distinct. The checker evaluates the inequality at each selected threshold, including the upper endpoint allowed by the release search. Every selected tick is below 10,000. The signed arc classifications at source indices 0, 5999, 34999, 124994, 124995, 128530, 128531, 132620, 132621 and 136742 agree with the release, span by span. The ten rounded means and every one of the 2,472 Fourier magnitudes at the eight harmonic sources match its C++ integers. At source zero the mean and harmonics 1 and 309 are −351116, 54603543 and 19145257. All 88 first passing orders agree with the release. The largest first passing Fourier order is 309 at degree 79. The smallest Fejér slack is 11613163/612250000000 there. At degree 89 the native credit exceeds 901/10¹² by 3259265478336753/41078464430947000000000000. A monotonicity proof covers higher degrees. In the independent adaptive Lean replay, raising 901 to 902 left degree 79 without a witness through order 309. The replay tested all 136,743 boxes and took 2,486.29 elapsed seconds at low priority. [Real soundness](HadwigerNelson/Stars/Partial/Certified.lean)
The four stock Lean checks evaluate `Stars.PartialCheck.checkShard` on disjoint source ranges. `beta_cell_of_checks` proves from these checks, layout and the kernel-evaluated degree table that every positive-degree star of the actual wave has the stated gain per incidence. The last shard also checks the 4,122 native-only rows across all 89 required degrees. The eleven degree-table modules use kernel reduction for all 88 finite Fejér tests. The highest-cost single-degree trial, at degree 79, used 22.94 CPU seconds.

| Certificate file under HadwigerNelson/Native | Declaration under Stars.PartialCheck.Native | Signed source indices (inclusive) | Elapsed seconds | CPU seconds |
| --- | --- | --- | ---: | ---: |
| PartialStars/Shard0.lean | `shard0` | 0–34,999 | 317.31 | 138.67 |
| PartialStars/Shard1.lean | `shard1` | 35,000–69,999 | 426.09 | 212.31 |
| PartialStars/Shard2.lean | `shard2` | 70,000–104,999 | 135.87 | 104.81 |
| PartialStars/Shard3.lean | `shard3` | 105,000–132,620 | 214.85 | 214.26 |

The [numbered blueprint](BLUEPRINT.md) records the declarations and their current status.

## Build and axiom audit

Run these commands from `hadwiger-nelson/lean/`.

```sh
lake build
lake env lean scripts/axioms.lean > axioms.log
python3 scripts/check_axioms.py axioms.log
```

The edge milestone at `6561378` passed a fresh default build from an empty project cache with pinned Mathlib dependencies. It took 1,977.83 seconds elapsed and 1,143.72 CPU seconds for 3,090 Lake jobs, concurrently with point-proof development. The independent clean build on Blaxel passed all 3,336 Lake jobs in **826.46 seconds elapsed** (13 min 46.5 s) and 2,904.29 CPU seconds. Its fresh Git clone contained the Lean package from proof revision `225cd7a`. We verified the complete package tree against Git object `b1e083f720c5fec6335ba3e9ca326474d3e14039` before building. The machine used cached artifacts for the pinned Mathlib dependencies and started with an empty Hadwiger–Nelson build directory. Reading all theorem dependencies took 12.56 seconds and the strict allowlist took 3.49 seconds. The axiom output was byte-identical to the independent local result (SHA-256 `f8775ffd29645bf32f02eb87fc4df2384f5ff194e4e83468f96fe7848e17cec5`). GitHub Actions runs the drawing definitions and Euclidean sanity examples. [CI workflow](../../.github/workflows/hadwiger-nelson-lean.yml)

At proof revision `225cd7a`, the full default build and strict allowlist passed. The audit checked 35 declarations and the Boolean goal of every one of the 25 native computations. The public edge theorem uses eight numerical checks, and the conditional point theorem uses the other seventeen. Each additional axiom in the following output is Lean 4.29.1’s generated native-evaluation axiom for the named Boolean check. The sources contain no admitted proofs, user-declared axioms, external implementations, unsafe proof paths or floating-point proof computations. [Audit script](scripts/check_axioms.py)

```text
'HadwigerNelson.edges_le_245510' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 HadwigerNelson.Angular.Native.block003._native.native_decide.ax_1_1,
 HadwigerNelson.Angular.Native.block004._native.native_decide.ax_1_1,
 HadwigerNelson.Angular.Native.block005._native.native_decide.ax_1_1,
 HadwigerNelson.Angular.Native.block006._native.native_decide.ax_1_1,
 HadwigerNelson.Angular.Native.block007._native.native_decide.ax_1_1,
 HadwigerNelson.Angular.Native.block008._native.native_decide.ax_1_1,
 HadwigerNelson.Stars.BoxCheck.complete_checked._native.native_decide.ax_1_1,
 HadwigerNelson.Stars.BoxCheck.sourceBoxes_checked._native.native_decide.ax_1_1]
'HadwigerNelson.points_le_10689_of_cited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 HadwigerNelson.Certificate.Hole.means_checked._native.native_decide.ax_1_1,
 HadwigerNelson.Certificate.Hole.packing_checked._native.native_decide.ax_1_1,
 HadwigerNelson.Certificate.ParameterBoxes.boxes_checked._native.native_decide.ax_1_1,
 HadwigerNelson.Angular.Partial.Native.block003._native.native_decide.ax_1_1,
 HadwigerNelson.Angular.Partial.Native.block004._native.native_decide.ax_1_1,
 HadwigerNelson.Angular.Partial.Native.block005._native.native_decide.ax_1_1,
 HadwigerNelson.Angular.Partial.Native.block006._native.native_decide.ax_1_1,
 HadwigerNelson.Angular.Partial.Native.block007._native.native_decide.ax_1_1,
 HadwigerNelson.Angular.Partial.Native.block008._native.native_decide.ax_1_1,
 HadwigerNelson.Centres.Quadrature.Native.mediumCoarse._native.native_decide.ax_1_1,
 HadwigerNelson.Centres.Quadrature.Native.mediumFine._native.native_decide.ax_1_1,
 HadwigerNelson.Centres.Quadrature.Native.smallIntervals._native.native_decide.ax_1_1,
 HadwigerNelson.Stars.PartialCheck.Layout.checked._native.native_decide.ax_1_1,
 HadwigerNelson.Stars.PartialCheck.Native.shard0._native.native_decide.ax_1_1,
 HadwigerNelson.Stars.PartialCheck.Native.shard1._native.native_decide.ax_1_1,
 HadwigerNelson.Stars.PartialCheck.Native.shard2._native.native_decide.ax_1_1,
 HadwigerNelson.Stars.PartialCheck.Native.shard3._native.native_decide.ax_1_1]
```

## Proof map

| Paper item | Lean declarations | Status |
| --- | --- | --- |
| Theorem 2 | `edges_le_245510` | Done |
| Theorem 1 | `points_le_10689_of_cited` | Done |
| Theorem 1 without the external hypothesis | `points_le_10689` | Open as an unconditional proposition |
| §1, Euclidean interpretation | `Plane`, `dist_three_fifths_four_fifths`, `unit_triangle_side_lengths`, `unit_triangle_no_two_colouring`, `edges_le_245510_one_colour_false`, `points_le_10689_one_colour_false` | Done |
| §5, sources of Theorem 26 | `Graph`, `Drawing`, `Drawing.crossingCount`, `Drawing.IsGood`, `crossingNumber`, `CitedFacts` | Done |
| Definition 4, Lemmas 5–6 | `Wave.Datum`, `Wave.colour`, `Wave.halfCopy_unique`, `Wave.completeDatum` | Done |
| Definition 7, Lemma 8 | `Placement.law`, `Placement.blankDensity_eq_integral`, `Placement.exists_zero_of_integral_lt_one` | Done |
| Lemmas 9–11 | `Placement.monoProb_eq_covariograms`, `Placement.monoProb_box` | Done |
| Proposition 12 | `Angular.checkGroup_integral_bound`, `Placement.meanMonoProb_of_bins_lower_pi` | Done |
| Theorem 3, consequence used in §4 | `Wave.complete_monoProb_upper`, `Wave.complete_ae_nonblank` | Done |
| Proposition 13, Lemmas 14–15, Corollary 16 | — | Replaced by the verified alternative above |
| §4, first milestone | `edges_le_245269` | Done |
| Lemma 20 | `Stars.one_bad_edge` | Done |
| Lemmas 21–22 | `Stars.real_fourier_star_bound`, `Stars.real_native_star_bound`, `Stars.fejer_bound` | Done |
| Lemmas 23–24 | `Stars.normalized_cell_box_sum`, `Stars.threshold_test`, `Stars.BoxCheck.cellScore_eight` | Done |
| Proposition 25, complete wave | `Stars.BoxCheck.complete_gain_of_check`, `Stars.complete_locked` | Done |
| §4, Theorem 2 | `complete_edge_bound`, `edges_le_245510` | Done |
| Lemma 17 | `Wave.hole_covariogram_bounds` | Done |
| Definition 18, Lemma 19 | `Wave.holeLower`, `Wave.holeLower_sound` | Done |
| Proposition 25, partial wave (§3.4) | `Stars.partial_locked` | Done |
| Theorem 26 | `Crossings.linear_lower` | Done |
| Lemma 27 | `Crossings.sample_lower` | Done |
| Lemma 28 | `Crossings.halving` | Done |
| Lemma 29 | `Crossings.degree_variance` | Done |
| Corollary 30 | `Crossings.edge_ceiling` | Done |
| Lemma 31 | `Packing.pointwise_degree` | Done |
| Lemma 32 | — | Replaced by the verified alternative above |
| Lemma 33 | `Packing.close_pairs` | Done |
| Lemma 34 | `Forest.blank_credit_lower` | Done |
| Lemma 35 | `Forest.candidates_acyclic` | Done |
| Lemma 36 | `Forest.two_tails` | Done |
| Lemma 37 | `Forest.max_sum_lower` | Done |
| Lemma 38 | `Forest.head_credit_lower` | Done |
| Lemma 39 | `Forest.short_credit_expectation` | Done |
| Lemma 40 | `Forest.unit_credit_expectation` | Done |
| Lemma 41 | `Forest.collision_upper` | Done |
| Lemma 42 | `Forest.collision_constants` | Done |
| Lemma 43 | `Crossings.weighted_degree_upper` | Done |
| Proposition 44 | `Forest.main_inequality` | Done |
| Lemma 45 | `Centres.doubled_pairs_lower` | Done |
| Lemma 46 | `Centres.rhombus_geometry` | Done |
| Lemma 47 | `Centres.candidate_geometry` | Done |
| Lemma 48 | `Centres.candidate_event` | Done |
| Lemma 49 | `Centres.probability_lower` | Done |
| Lemma 50 | `Centres.admissible_budgets` | Done |
| Lemma 51 | `Centres.orientation_budgets` | Done |
| Proposition 52 | `Centres.credit_lower` | Done |
| §9, wave data and constants | `Certificate.partialConstants`, `Certificate.partial_mono_probability`, `Certificate.partial_blank_density` | Done |
| Proposition 53 | `Certificate.point_boxes_sound`, `Certificate.point_bound_lt_one` | Done |
| §9, Theorem 1 assembly | `Point.six_colour_of_point_estimates`, `Proof.points` | Done |


## Open problems

Both requested theorems are proved. Discharging `CitedFacts` would give the unconditional point theorem. This requires proofs of the two published crossing bounds and the comparison and attainment properties of planar drawings. The alternative height quadrature and stronger planar packing estimates do not enter the certified bounds.

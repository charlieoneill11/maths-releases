# Hadwiger–Nelson proof map

The primary target is a six-colouring for any finite list of at most 245,510 unit edges. The point bound gives a six-colouring on any set of at most 10,689 points, assuming `CitedFacts`. The paper numbers below are from the 24 November 2026 release, revision `7541cf08200934aecee19c1551539f06d4af723e`. [Paper and certificate programs](https://github.com/charlieoneill11/maths-releases/tree/7541cf08200934aecee19c1551539f06d4af723e/hadwiger-nelson)

## Current Lean declarations

Names on this page are relative to `HadwigerNelson`. Charlie approved the two public files at revision `3c939db`. Both public theorems and their per-theorem axiom allowlists passed.

| Paper item | Declaration in the worktree | Status |
| --- | --- | --- |
| Theorem 2 | `edges_le_245510` | Done. `Proof.edges` applies the certified `complete_edge_bound`. |
| Theorem 1 | `points_le_10689_of_cited` | Done. The public proof combines the critical-subset reduction, forest and centre estimates, and certified objective bound. |
| Theorem 1 without the external hypothesis | `points_le_10689` | Defined as a `Prop`. The unconditional statement would require additional proof. |
| §1, Euclidean interpretation | `Plane`, `dist_three_fifths_four_fifths`, `unit_triangle_side_lengths`, `unit_triangle_no_two_colouring`, `edges_le_245510_one_colour_false`, `points_le_10689_one_colour_false` | Definition and sanity lemmas implemented. |
| §5, sources of Theorem 26 | `Graph`, `Drawing`, `Drawing.crossingCount`, `Drawing.IsGood`, `crossingNumber`, `CitedFacts` | Definitions and external hypothesis present. The four fields express the crossing lower bound, the 5-planar edge bound, comparison with a finite-intersection drawing, and existence of an optimal good drawing. |

[Statement](HadwigerNelson/Statement.lean) · [Proof assembly](HadwigerNelson/Proof/Bounds.lean) · [Euclidean sanity checks](HadwigerNelson/Sanity.lean) · [Drawing definitions and cited hypotheses](HadwigerNelson/Cited.lean)

## Edge proof

Verified components now include the colour-class decomposition, the twelve half-tile representatives, both literal wave profiles, the one-bad-edge repair, Fejér inequality, threshold implication, and sound integer rounding steps. Both the 245,269-edge milestone and the full 245,510-edge theorem passed Lake and their per-theorem axiom audits.

| Paper item | Lean declarations | Status |
| --- | --- | --- |
| Definition 4, Lemmas 5–6 | `Wave.Datum`, `Wave.colour`, `Wave.halfCopy_unique`, `Wave.completeDatum` | Done. Checked the complete wave data, tile periodicity, null seams, symmetry, and all twelve physical copies. |
| Definition 7, Lemma 8 | `Placement.law`, `Placement.blankDensity_eq_integral`, `Placement.exists_zero_of_integral_lt_one` | Done. Uniform placements on the fundamental rectangle, blank density and derandomisation. |
| Lemmas 9–11 | `Placement.monoProb_eq_covariograms`, `Placement.monoProb_box` | Done. Two physical overlaps in the first quadrant and their slice enclosures, including the case of a vertical offset at least H. |
| Proposition 12 | `Angular.checkGroup_integral_bound`, `Placement.meanMonoProb_of_bins_lower_pi` | Done. Both offsets, arctangent bin lengths and outward-rounded sums are related to the integral. |
| Theorem 3, consequence used in §4 | `Wave.complete_monoProb_upper`, `Wave.complete_ae_nonblank` | Done. The complete wave satisfies the required probability bound and almost surely colours each fixed vertex. |
| Proposition 13, Lemmas 14–15, Corollary 16 | — | The alternative height quadrature is outside the chosen proof. |
| §4, first milestone | `edges_le_245269` | Done. Completed and audited with six native angular checks. |
| Lemma 20 | `Stars.one_bad_edge` | Done. Finite recolouring and the expectation inequality. |
| Lemmas 21–22 | `Stars.real_fourier_star_bound`, `Stars.real_native_star_bound`, `Stars.fejer_bound` | Done. Angular Fourier bounds for the physical responses, the same-colour bound and the finite Fejér inequality. |
| Lemmas 23–24 | `Stars.normalized_cell_box_sum`, `Stars.threshold_test`, `Stars.BoxCheck.cellScore_eight` | Done. Sum of disjoint physical boxes and degree threshold tests. |
| Proposition 25, complete wave | `Stars.BoxCheck.complete_gain_of_check`, `Stars.complete_locked` | Done. Physical classification, normalized Fourier rows, degree coverage and the gain per incident edge. |
| §4, Theorem 2 | `complete_edge_bound`, `edges_le_245510` | Done. Completed and audited with six angular checks and two star checks. |

Theorem 3 in the paper gives the particular bound `p_E = 4.077146893978·10⁻⁶` for an everywhere-defined colouring. The reproduced `2²⁸`-bin C++ trial gives `4.077151575141432·10⁻⁶`, which is below both `1/245269` and `1/245510 + β_E/2`, but above the printed `p_E`. The certified probability bound implies both strict numerical inequalities in Lean.

## Conditional point bound

| Paper item | Lean name | Status |
| --- | --- | --- |
| Lemma 17 | `Wave.hole_covariogram_bounds` | Done. Relate two simultaneous blanks to the hole covariogram and establish the coordinate symmetries and monotonicity used below. |
| Definition 18, Lemma 19 | `Wave.holeLower`, `Wave.holeLower_sound` | Done. Define Ω by rational slice enclosures and prove that it bounds the normalised overlap from below. |
| Proposition 25, partial wave (§3.4) | `Stars.partial_locked` | Done. Physical Fourier and Fejér estimates establish `β_V = 901·10⁻¹²` from the four signed source checks and the layout check. |
| Theorem 26 | `Crossings.linear_lower` | Done. Use the four fields of `CitedFacts` to obtain `cr(G) ≥ 6M − (266/9)(N−2)` for a simple graph with at least three vertices. |
| Lemma 27 | `Crossings.sample_lower` | Done. Sample an induced `k`-vertex subgraph of an optimal good drawing. Four distinct endpoints survive with probability `P₄`, which is positive for `4 ≤ k ≤ n`. |
| Lemma 28 | `Crossings.halving` | Done. Select one edge from each parallel pair in a loopless drawing of multiplicity at most two and apply the simple-graph bound. |
| Lemma 29 | `Crossings.degree_variance` | Done. For nonisolated degrees at least three, count crossings among consecutive arcs of unit circles and bound the sum of squared degree deviations. |
| Corollary 30 | `Crossings.edge_ceiling` | Done. Specialise the variance to 10,689 points with the paper’s degree hypothesis and certify the ceiling of 403,078 edges. |
| Lemma 31 | `Packing.pointwise_degree` | Done. Bound the number of nearby neighbours of each point in a strictly separated set by `k_ϱ(t)`. Summing yields the average bound used here. |
| Lemma 32 | — | The stronger average degree bounds 6 and 8 use planarity and 1-planarity. Both point-certificate replays passed with `g_ϱ` replaced by the pointwise `k_ϱ`. This proof uses Lemma 31 for average degrees and adds no plane-graph field to `CitedFacts`. |
| Lemma 33 | `Packing.close_pairs` | Done. Bound the numbers of short pairs for the nested separated sets, with certified rational estimates. |
| Lemma 34 | `Forest.blank_credit_lower` | Done. Turn the two-blank lower bounds into valid credits for short and nearly vertical unit edges. |
| Lemma 35 | `Forest.candidates_acyclic` | Done. Prove the potential increases on each directed candidate edge and that selecting at most one incoming edge per vertex gives a forest. |
| Lemma 36 | `Forest.two_tails` | Done. Two distinct eligible tails in the inner separated set with the same head are almost never simultaneously blank. |
| Lemma 37 | `Forest.max_sum_lower` | Done. Bound the larger of the short credit and the sum of unit credits after losses. |
| Lemma 38 | `Forest.head_credit_lower` | Done. Accounted for incoming short, unit and centre events, including the null set of exceptional translations. |
| Lemma 39 | `Forest.short_credit_expectation` | Done. Integrate short-edge credits over orientations for each layer. |
| Lemma 40 | `Forest.unit_credit_expectation` | Done. Bound the expected sum of excess credits for eligible unit edges. |
| Lemma 41 | `Forest.collision_upper` | Done. Bound the loss when two eligible tails share a unit neighbour. |
| Lemma 42 | `Forest.collision_constants` | Done. Sum collision losses for the two modes using the pointwise packing bound and certify upper bounds `L, T, U, J`. |
| Lemma 43 | `Crossings.weighted_degree_upper` | Done. Apply Cauchy–Schwarz to the centred degrees and the two nonzero weights, using Lemma 29 with `k = 2090`. |
| Proposition 44 | `Forest.main_inequality` | Done. Derive `1 ≤ Ψ(m,s,j)` from the expected forest scores for both profiles and Proposition 52 for centre credit. |
| Lemma 45 | `Centres.doubled_pairs_lower` | Done. Count doubled pairs by retaining one arc of each pair, then apply sampling with `k = 1317`. |
| Lemma 46 | `Centres.rhombus_geometry` | Done. Relate chord length to centre separation, the common midpoint and the minor-arc criterion. |
| Lemma 47 | `Centres.candidate_geometry` | Done. Identify the centre arc, uniqueness at its head, the potential increase and exclusion of competing unit candidates for medium chords. |
| Lemma 48 | `Centres.candidate_event` | Done. Almost every translation in the centre event leaves the two endpoints blank and no unit candidate entering the head has a blank tail. |
| Lemma 49 | `Centres.probability_lower` | Done. Bound the physical centre-event probability, integrated over rotation and translation, in both chord regimes and profiles. |
| Lemma 50 | `Centres.admissible_budgets` | Done. Prove the candidate bounds for `b_R` and `b_D` using close-pair and incidence counts. |
| Lemma 51 | `Centres.orientation_budgets` | Done. Bound the number of eligible orientations and their total excess angle, including all seven long-single thresholds. |
| Proposition 52 | `Centres.credit_lower` | Done. Combine Lemmas 49–51 to bound the expected number of centre edges. |
| §9, wave data and constants | `Certificate.partialConstants`, `Certificate.partial_mono_probability`, `Certificate.partial_blank_density` | Done. Verify the partial-wave profile, obtain `q` and `p` (Proposition 12, `N = 2²⁶`), and certify `B, C, E, L, T, U, J, ρ₁, ρ₂` with the chosen packing bounds. |
| Proposition 53 | `Certificate.point_boxes_sound`, `Certificate.point_bound_lt_one` | Done. Cover every feasible integer triple `(m,s,j)` and prove `Ψ < 1`. Use the displayed mixed-endpoint variance estimate on each box. The reference box count and maximum are regression data for the paper’s constants. |
| §9, Theorem 1 assembly | `Point.six_colour_of_point_estimates`, `Proof.points` | Done. Take a minimal counterexample, pad with isolated points, use Corollary 30, then contradict Proposition 44 with Proposition 53. |

# Proof blueprint

| Paper | Lean declaration | Status |
| --- | --- | --- |
| Proposition 3 | `CitedFacts.maynard` | Approved hypothesis |
| Lemma 4 | `divisor_reduction` | Done |
| Theorem 5 | `CitedFacts.donnellyGrimmett` | Approved hypothesis |
| Lemma 6 | `divisor_of_revealed`, `revealed_of_divisor` | Done |
| Lemma 7 | `stickLaw_absolutelyContinuous`, `stickLaw_frontier_E_null`, `stickLaw_frontier_F_null` | Done |
| Proposition 8 | `eventually_density_lower`, `eventually_density_upper` | Done |
| Lemma 9 | `p_complement`, `q_complement` | Done |
| Lemma 10 | `p_recursion`, `q_recursion` | Done |
| Lemma 11 | `p_one_rescaled`, `q_one_rescaled`, `p_two`, `q_two` | Done |
| Lemma 12 | `cell_bounds` | Done |
| Lemma 13 | `hermite_hadamard_inv`, `hermite_hadamard_inv_nonpos`, `reciprocal_affine_decreasing_iff` | Done |
| Proposition 14 | `lowerP_sound`, `upperQ_sound`, `Checker.checkWindow_sound`, `p6_Tin`, `q5_Tout` | Done |
| §6 | `main_of_cited`, `density_lower_of_cited`, `density_upper_of_cited` | Done |

Proposition 8 uses eventual strict inequalities at thresholds strictly below the lower probability
or strictly above the upper probability. `Checker.checkWindow_sound` connects each native Boolean
equality to the corresponding real probability inequality.

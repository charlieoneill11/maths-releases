# Proof blueprint

`Blueprint.lean` checks the declarations listed below and the exact types of the three main theorems. Run it with `lake env lean Blueprint.lean`.

| Paper item | Lean name | Proof work |
| --- | --- | --- |
| Lemma 7 | `Legendre.powerEndpoint_ne_prime`, `Legendre.powerInterval_iff` | Proved in `Legendre/Statement.lean` |
| Lemma 8 | `prime_in_shifted_square` | Half-square witnesses and integral endpoints |
| Proposition 3 | `low_range` | Smooth increase of the power and exact integer cutoffs |
| Lemma 9 | `square_interval_nested` | Ceiling and the derivative of the power |
| Lemma 10 | `prime_in_cms_interval` | Closed CMS interval inside the desired open interval |
| Corollary 11 | `far_range` | Monotone comparison and a rational bound at the cutoff |
| Definition 12 | `Legendre.CosineTest` | Defined in `Legendre/AnalyticData.lean` |
| Lemma 13 | `cosine_fourier_spec` | Integrals of products of cosines and compact-support Fourier estimates |
| Lemma 14 | `smoothed_explicit_formula` | Integration by parts and the limit of the Davenport remainder |
| Lemma 15 | `zeroCount_error` | The Trudgian field followed by a scalar estimate |
| Lemma 16 | `zero_sum_bound` | Weighted integration by parts and variation integrals |
| Proposition 17 | `gap_condition` | Smoothed formula, zero sum, and bounds for the error terms |
| Lemma 18 | `shoulder_lengths` | Mean value estimates |
| Lemma 19 | `twelve_mode_bounds` | Interpolation, exact checkers and analytic tails |
| Lemma 20 | `twelve_mode_cell_bounds` | Checked cosine enclosures and monotone heights |
| Lemma 21 | `shoulder_sum_bound` | Layer decomposition and Brun–Titchmarsh |
| Proposition 22 and Table 1 | `bridge_row_checks`, `bridge_error_bounds`, `bridge_range` | Verified numerical bounds and the contradiction for `Jₖ` |
| Theorem 4 | `outer_of` | Combine `bridge_range` and `far_range` |
| Lemma 23 | — | Optional BLS certificate replay, outside this implementation |
| Theorem 2 | `squares_of` | Published prefix and the square computation |
| Proposition 5 | `finite_range` | Square nesting and the power computation |
| Theorem 1 | `main_of` | Low, finite and large ranges |

The smoothing lemma takes the lower support endpoint to be at least 2, as in its application in Proposition 22. The zero-sum lemma takes the two derivative-weight integrability bounds proved for cosine transforms. Decay of the transform gives integrability of its mass and logarithmic moment. The `gap_condition` statement uses the empty correction set required by Proposition 22.

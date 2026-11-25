# Chowla formalisation blueprint

`lake build` checks the statement library and proofs. The declaration map can
also be checked with `lake env lean -DautoImplicit=false Blueprint.lean`.

| Paper item | Lean declaration | Status |
| --- | --- | --- |
| Equation (1), Theorem 1 | `IsFundDisc`, `chi`, `DiscClass`, `InClass`, `discs`, `ClassStatement`, `MainStatement` | Done |
| Character and discriminant examples | `chi_neg_four`, `chi_eight`, nine `IsFundDisc` sanity lemmas | Done |
| General character properties | `chi_odd_prime`, `chi_two`, `chi_neg_one`, `chi_primitive` | Done |
| Lemma 4 | `even_central_order` | Done |
| §2.3 | `ZeroCopy`, `zeroSummand`, `zeroStatistic`, `zeroStatistic_summable` | Done |
| Definition 5 and equation (3) | `fourier`, `IsProfile`, `radius`, `oddProfile`, `delta`, `cumulant`, `modelMoment` | Done |
| Lemma 6(a–d) | `delta_eq_zero_of_support`, `abs_delta_le`, `delta_mul_delta_eq_zero`, `cumulant_continuity` | Done |
| Theorem 7, empty pattern | `PaperClaims.emptyPatternMoments` | Named hypothesis |
| Lemma 8, empty pattern | `squarefree_shell_mass`, `sharpShell_mass_deficit` | Done |
| §4.1 and equation (11) | `modelExpectation`, `centered`, `wick`, `modelExpectation_monomial`, `centered_moment` | Done |
| Definition 20 and equation (12) | `legendreProfile`, `Row.Admissible`, `IsAmplitude`, `amplitudeAt`, `H`, `G`, `inner_G`, `inner` | Done |
| Lemma 21 | `integral_H`, `extremal_cumulant` | Done |
| Theorem 22 | `smoothProfile_properties`, `pointwise_vanishing_bound`, `variational` | Done |
| Lemma 23 | `chain` | Done |
| Lemmas 24–25 | `connected_partitions`, `contraction_formula`, `equal_width_matching_count` | Done |
| Corollary 26 | `innerGRow_eq_cumulant` | Done |
| §7.1 and Lemma 27 | `integral_truncatedPower`, `convolution_truncatedPower`, `Spline.primitive_sound`, `Spline.convolution_sound`, `cumulant_covariance` | Done |
| Lemma 28 | `cumulant_shift`, `lowerPrimitive_oddProfile` | Done |
| Legendre profiles | `legendre`, `legendreProfile_integral`, `legendreProfile_bound` | Done |
| Lemmas 29–31 | `Hstar_pointwise_error`, `Hstar_integral_error`, `central_error`, `cot_upper` | Done |
| §8.1, amplitude data | `Rows`, `PaperRows`, `rows_r*_eq`, `r1Grid_agrees`, `F₈`, `final_amplitude_admissible` | Done |
| Proposition 32 | `StageBounds`, `early_stage_gain`, `late_stage_gain`, `certificate_stage` | Done |
| Milestone 1 | `CertificateStatement`, `certificate` | Done |
| §8, sharp count | `sharp_count_of_weighted`, `discs_partition` | Done |
| Milestone 2 | `main_class_of`, `main_of` | Done under the stated hypotheses |

## Dependencies

The cumulant and model work supplies the marked contraction formulas. The spline
work supplies the exact evaluation and approximation bounds. The certificate
checker needs both. The character work uses the stated GRH and cited facts and
supplies the zero statistic and the parity lemma to the variational proof. The
variational proof uses the model continuity and the empty-pattern moment claim.
The final count combines it with the sharp shell asymptotic and the certificate.

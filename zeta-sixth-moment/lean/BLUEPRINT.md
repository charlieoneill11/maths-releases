# Sixth moment certificate blueprint

The Lean target for Theorem 2 is conditional on `PaperPairings`, the conclusion of the paper's analytic theorems. The region masses, projection argument, and rational exponent covering can be checked independently of those analytic inputs.

[Statement.lean](ZetaSixth/Statement.lean), [Regions.lean](ZetaSixth/Regions.lean), [Claims.lean](ZetaSixth/Claims.lean), and [Exponents.lean](ZetaSixth/Exponents.lean) define the statement interfaces. [Blueprint.lean](Blueprint.lean) records the principal proof obligations as propositions. Names in the table are relative to `ZetaSixth` unless qualified.

| Paper item | Lean declaration | Status |
| --- | --- | --- |
| Introduction and Theorem 2 | `zetaLine`, `M6`, `localFactor`, `a3`, `c3`, `C`, `MainBound` | Frozen |
| Euler factor identity and product checks | `localFactor_closedForm`, `a3_multipliable`, `a3_pos` | Complete |
| Coefficient bracket | `C_bounds` | Complete |
| §2.1 and Lemma 4 | `Ω`, `v`, `J`, `chamberVolume`, `μ`. Proofs of `J_involutive`, `J_mem_Ω`, `J_measurePreserving`, `v_comp_J`, `mu_finite` | Complete |
| §4, §5, §6, §8, §10 | `Dacc`, `A`, `S3`, `marked`, `N0`, `balanced`, `PPlus`, `FPlus`, `U7`, `ceiling` | Frozen |
| §9 mass table | `intermediateMasses` | Exact reference values transcribed |
| Lemma 4 | `mu_Omega` | Complete |
| Theorems 16, 23, 52, 67 and 79, measure paragraphs | `U7_complement_ae`, `mu_U7_from_loss`, `mu_N0`, `mu_U7` | Complete |
| Theorem 79, Table 1 | `mu_mixedCells`, `Cell.integral_eq`, `seven_reflected_masses`, `seven_reflected_total` | Complete |
| Proposition 3 and §10 | `ceiling_complement_ae`, `mu_ceiling_reduction`, `mu_ceiling`, `ceilingMass_lt`, `projection_ceiling`, `projection_ceiling_exact` | Complete |
| Reflection and containment checks | `J_U7`, `J_ceiling`, `U7_subset_ceiling` | Complete |
| Definition 7 | `Test`, `Weight`, `timeNorm`, `numerator`, `gram`, `Profile`, `Family`, `Faithful`, `familySpan` | Frozen |
| Theorems 16, 23, 52, 67 and 79, analytic input | `PaperPairings` | Frozen |
| Proposition 8 | `projection_principle`, `bound_of_indicator` | Complete |
| §9 and Theorem 2 | `main_of` of type `ConditionalMain` | Complete, conditional on `PaperPairings` |
| Lemmas 82–89 | `Exponents.Degrees` and its constraints, budgets and margins | Frozen |
| Lemmas 83–90 | Named `ring` identities and paper-to-Lean source audit | Kernel proofs complete |
| Lemma 90(i)–(iii) | `Exponents.lemma90` of type `Exponents.Lemma90` | Proof complete |
| After Lemma 90 | `Exponents.lemma90_covering` of type `Exponents.Covering` | Proof complete |
| Optional Z4, §3 and Theorem 1 | Separate Fraccaro hypothesis, Dixon–Anderson bridge, span, least-squares solution and eventual bound | Deferred |

The mass proof integrates polynomials over ordered affine faces in the volume-preserving coordinates `(k,x,z)`. Set identities identify the paper's regions with finite unions of these cells up to null affine hyperplanes. The exponent proof uses a soundness theorem for weighted sums of rational affine inequalities evaluated on real tuples. Lean checks the certificate data and derives the exact cell values.

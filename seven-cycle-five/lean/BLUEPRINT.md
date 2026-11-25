# Seven-cycle proof blueprint

The public declarations are in `SevenCycle.Statement`. Their hypotheses reduce to `Proof.packing Proof.cycleStep`, the version used by the proof modules. The table lists Lean declarations in `SevenCycle.Blueprint` unless it gives a different namespace. All entries in the table are proved.

| Paper | Lean declarations | Role |
| --- | --- | --- |
| Graph interpretation | `SevenCycle.Graph.sevenCyclePower`, `Graph.isCode_iff_isIndepSet`, `Graph.indepNum_four_le_112`, `Graph.indepNum_five_le_392` | Codes are precisely the independent sets in the corresponding strong graph power. |
| §2 group and projections | `Isometry`, `act`, `act_confusable`, `isometry_orders`, `dropCoord` | Signed permutations with translations. Deleting a coordinate preserves the order of the others. |
| Lemma 3 | `band_projection`, `band_card`, `sum_band_card`, `alternating_band_sum`, `band_bound` | Project each two-level band injectively to a code. Each word is in exactly two bands. |
| Corollary 2 | `SevenCycle.Proof.five_of_four`, `SevenCycle.card_le_392` | Instantiate the band bound with 112 in dimension four. |
| Lemma 4 | `deficit_sum`, `level_from_deficits`, `deficits_one`, `deficits_two`, `deficits_three` | Level bounds, consecutive starts with a large centre, and the intervening band for gap two. The upper bound in dimension three is an explicit hypothesis. |
| Definition 5 | `HasCentre`, `AxisGap`, `HasProfile`, `profile_exists` | The profile is the multiset of the four least cyclic distances. |
| Lemma 6 | `card_le_ten`, `twoRepresentatives`, `atlas_two` | Bound codes in two dimensions and cover ten-word codes by the three explicit orbits. The public example gives the lower bound. |
| Theorem 7 | `card_le_thirty_three`, `atlas_complete`, `atlas_row_valid`, `atlas_rows_inequivalent`, `atlas_stabilizers` | Decode the actual seven-plane masks. Show every maximum code belongs to a listed orbit and that each row represents a different valid orbit. |
| Lemma 8 | `crossings` | The two orders of cutting bands give the same set on the surviving axes. |
| Lemma 9 | `slabs`, `slabs_transverse` | Reconstruct the three levels around a centre and constrain transverse projections. |
| Lemma 10 | `perfect_matching`, `matching_count` | Obtain a matching by Hall's theorem and count unused edges for any perfect matching. |
| Lemma 11 | `normalise_full_pair` | Position the marked starts and put the first projected band in the literal atlas. |
| Proposition 12, Lemmas 13–14 | `SearchSpec.exclude_adjacent`, `SearchSpec.exterior_card_le_112`, `SearchSpec.mixed_no_remaining` | All six stages retain actual configurations. `Adjacent.FrontSearch.adjacent_bound` derives the bound for all ten profiles from the exhaustive front check. `Adjacent.FrontSearch.anchor_of_run` supplies the recorded slab from a full positive front check. `Adjacent.RecordedFrame.bound1111` and `Adjacent.MixedCommon.reject` close the four-adjacent and mixed cases from these records. |
| Proposition 15, Lemma 16 | `SearchSpec.exclude_two`, `SearchSpec.two_no_join` | The planar filter and any chosen perfect matching retain the genuine middle layout. `TypeTwo.Search.all_chunks` checks the six-band join over all 64 normalized intervals, and `TypeTwo.Search.exclude_two_of_chunks` transports the numerical coverage back to every marked code with minimum profile entry two. |
| Proposition 17, Lemma 18 | `SearchSpec.exclude_three`, `SearchSpec.three_no_join` | Rule out four pairs of full starts at distance three without a size hypothesis. `TypeThree.no_join` certifies all twenty normalized search parts, and `TypeThree.exclude` transports this result to every code. |
| §8, Theorem 1 | `no_code_113`, `reduce_to_113`, `SevenCycle.Proof.bound_four`, `SevenCycle.card_le_112` | Exclude size exactly 113 by the profile split. Any larger code contains a code of size 113. |

## Computational proof interfaces

`SearchSpec` states retention lemmas for the individual stages. It represents a projection by setting the deleted coordinate to zero, so a twice-projected word retains its ambient axis labels. A frame records the axis gaps and the base height for each pair of marked starts. These predicates describe labelled configurations before atlas and stabiliser reductions.

The plane and cube operations have decoding proofs. In the atlas search, `Atlas.CubePlanes.normalizedCheckUsing_sound` shows that every genuine cube follows a searched branch. At a 33-word leaf, `Atlas.Leaves.atlasLeaf_sound` verifies the actual atlas row and motion. The twelve exclusion checks and twenty-four classification checks are complete.

For the physical adjacent joins, `Adjacent.MixedSlabs.two_sound` and `three_sound` retain every compatible pair or triple of supplied slabs. `Adjacent.Stage6.noRemaining` excludes every row of the two nonempty mixed union tables. All 65 search intervals prove `Adjacent.FrontSearch.checked`. Its retention proof establishes that every actual anchor reaches its slab row. Lemmas 13 and 14 apply these rows in the physical frame of a marked code. The type-two and type-three numerical checks cover all opposite atlas classes or all source residues and query-slot parts. Each complete native fact proves a Boolean equality under `SevenCycle/Native/`. The report lists each check and its timing, the comparison with the paper, and the public axiom audit. [Report](REPORT.md)

# Seven-cycle formalisation report

Charlie signed off on the public statement at commit `b063e6d`. The approved `SevenCycle/Statement.lean` has blob `e69d4ca67b37c33b1df5aeef82b5785e0e0660f1`. Lean proves every four-dimensional code has at most 112 words, and every five-dimensional code has at most 392. [Draft PR](https://github.com/charlieoneill11/maths/pull/50)

| Input | Pin |
| --- | --- |
| Lean | v4.29.1, commit `f72c35b3f637c8c6571d353742168ab66cc22c00` |
| Mathlib | v4.29.1, commit `5e932f97dd25535344f80f9dd8da3aab83df0fe6` |
| Paper and oracle programs | `charlieoneill11/maths-releases` at `7541cf08200934aecee19c1551539f06d4af723e` |
| Released atlas TSV, SHA-256 | `aee14d35c2f1ef09e27a1e65852d96499ad902fe6cfcda436fcc91078172e38a` |
| Released 105-word witness, SHA-256 | `d56999bb4be86de2e4d0769db64415a56a8313bc4ec94dd95f2248cc889ae46c` |

## Proof status

The [blueprint](BLUEPRINT.md) gives the Lean names corresponding to each paper item.

| Paper item | Status | Evidence |
| --- | --- | --- |
| Definitions and sanity lemmas | done | Kernel-checked codes of sizes 3, 10, 33 and 105, the one-dimensional upper bound and the specified confusable pair. |
| Graph interpretation | done | `SevenCycle.Graph.isCode_iff_isIndepSet` identifies codes with independent sets in the strong power of Mathlib’s seven-cycle graph. The independence-number bounds inherit the public proof dependencies. |
| §2 group and projections | done | Signed permutations act invertibly and preserve confusability. The two group orders are proved. |
| Lemma 3 | done | Injectivity, code preservation, double counting, alternating sum and the dimension recurrence. |
| Corollary 2 from Theorem 1 | done | `SevenCycle.Proof.five_of_four` uses only the three standard axioms. The unconditional corollary follows by applying it to the four-dimensional bound. |
| Lemma 4 and Definition 5 | done | All three parts, with the dimension-three bound as an explicit hypothesis, and existence of a profile. The centre check covers every weak composition of five into seven parts. |
| Lemma 6 | done | The upper bound 10 follows from band averaging. A kernel-checked witness attains it. The kernel checks all 9,261 normalized planar parameter tuples, with explicit orbit witnesses for the 20 feasible ones. |
| Theorem 7 | done | Every literal row has 33 words and is a code. A numerical isometry invariant distinguishes all 1,016 rows. A checked census gives the stabiliser orders of all rows. All 12 normalized searches exclude 34 words. The explicit witness attains the upper bound of 33. All 24 census chunks passed. Every 33-code normalizes to a leaf and each accepted leaf is equal, plane for plane, to an isometric image of a literal atlas representative. |
| Lemmas 8–11 | done | Crossings, slabs, arbitrary-matching count, normalisation. Hall’s argument takes the dimension-three bound, and normalisation takes atlas completeness. |
| Bitsets | done | Semantics of membership, union, intersection, neighbourhood, shifts, levels, cuts, isometries, and cardinality. The regression module checks wrapping, padding bits and coordinate projections. |
| Proposition 17 and Lemma 18 | done | All twenty full-domain checks prove `TypeThree.no_join`. Atlas completeness and frame normalization give the unrestricted geometric exclusion `TypeThree.exclude`. |
| Proposition 15 and Lemma 16 | done | All three retention proofs cover actual marked codes, including the restrictions for any chosen perfect matching. All 66 native facts passed. The 64 intervals partition the opposite atlas classes. Orbit normalization and the three-dimensional bound transport the result to every 113-word code with minimum profile entry two. |
| Proposition 12 and Lemmas 13–14 | done | All six stages retain genuine marked codes. The 65 front checks supply a classified slab at every adjacent axis. The physical joins bound 1111 by 112, rule out the 1112 triples, and cover the 4 unions of 1122 and 64 unions of 1123. Every one of the 68 unions has an impossible marked band. The six other mixed profiles have empty source tables. |
| §8 and Theorem 1 | done | A 113-word code has a profile. The adjacent, type-two and type-three propositions exclude every possible profile. A larger code would contain a 113-word subcode. |

## Open questions

The 105-word witness and the upper bound leave the four-dimensional maximum in the interval 105–112. Determining its exact value remains open here.

## Verified computations and comparisons

| Quantity | Comparison | Evidence |
| --- | --- | --- |
| Witness sizes 3, 10, 33 and 105 | equal | The 33-word witness is the first atlas row. Projecting its first two planes gives 10. The 105-word witness is the file in the release. |
| Normalized 33-code leaves | equal | Two independent diagnostic enumerations produced the same 6,535 normalized cubes. Lean checked the indicated full group image for all 6,535 in 248.31 s under load. The separately proved traversal of all 90 representative/pattern pairs certifies completeness. |
| Labelled 33-word codes | equal | A separately compiled enumerator counted 2,844, 918 and 2,773 normalized leaves in the three planar orbits. Weighting by seven translations and planar orbit sizes 392, 196 and 392 gives 16,672,544, as in Theorem 7. This count is a diagnostic. The Lean completeness proof checks the individual leaves. |
| Three-dimensional maximum | equal | The explicit witness attains 33. Each of the 12 normalized 34-word searches rejects every possible completion. |
| Group orders 392 and 16,464 | equal | Follows from the explicit permutation, sign and translation coordinates. |
| Seven deficits summing to five | equal | Kernel enumeration of all 462 weak compositions. |
| Atlas transcription | equal | The 1,016 rows and 7,112 masks exported from Lean reproduce the original TSV byte-for-byte. |
| Validity of released rows | equal | All 1,016 rows passed the proved 33-word checker. |
| Inequivalent released rows | equal | All 1,016 values of the proved isometry invariant are distinct. The 24 normalized traversal checks separately certify coverage. |
| Distinct gap-three pairs | equal | An independent replay reproduces all 21,378,687 physical pairs in Lemma 18. The five nontrivial stabilisers account for all 254,589 additional descriptions in the reference program. |
| Gap-three reference replay | equal | The untrusted program reproduced 348,488 phases, 21,633,276 descriptions and zero surviving joins in 83.84 s with peak RSS 1.17 GiB. |
| Adjacent Stage 1, second representative 0 | equal | A benchmark counted 23,156 passing pairs among 16,727,424 comparisons, agreeing with C++. This timing experiment does not certify the final search. |
| Stabiliser orders | equal | Exhausting all 16,464 isometries per row gives 1,011 trivial stabilisers, one of order two, three of order three and one of order six. |
| Profile 1111 oracle unions | equal | The source programs reproduced 1,776 unions. On these inputs a greedy box cover gives bounds of 101–106. This is a different criterion from the paper’s exact exterior optimisation. Lean verifies the 112 bound for every supplied union in four chunks, including transport back to the original frame. The complete front search supplies a classified slab at each active axis. The verified physical join covers all compatible placements. |
| Mixed adjacent physical joins | equal | Lean checks the 138, 48 and 395 source slabs for profiles 1112, 1122 and 1123. The compatible unions belong to tables of sizes 0, 4 and 64, as in the release. |
| Remaining mixed bands | equal | An independent exhaustive search found an individually impossible marked band in each of the 68 unions. Lean verifies 40 binary branch or clique-cover nodes for 1122 and 356 for 1123. The largest certificate has 27 nodes. |
| Type-two planar survivors with opposite representative 0 | equal | Lean found 12,113 support pairs and 65,557 planar placements in 16,727,424 labelled comparisons. The placements split into 21,160 of profile 2222 and 44,397 mixed profiles. |
| Type-two middle layouts with opposite representative 0 | equal with the released matching, different with the alternate matching | The released matching gives 7 mixed and 0 pure survivors. Sorting both the source and transformed target coordinates before matching gives 4 mixed and 0 pure survivors in both Lean and an independent C++ replay. Three of the mixed layouts are shared. All eight layouts in the union fail the final projection join. |
| Gap-three cuts of released representatives | new cross-check | All 21,336 triples of row, axis and start have different cuts at that start and three steps later. The kernel-checked soundness theorem interprets each mask. |

### Adjacent and type-two search details

The fused adjacent search retains all six transverse bands of an actual marked code. It indexes the supplied prefix hints. An absent hint passes the layout to the terminal checker, so the hints cannot discard an actual code. `Adjacent.FrontSearch.anchor_of_run` converts its Boolean result to a recorded middle layer and slab for each active axis. In one physical frame, `Adjacent.RecordedFrame.bound1111` proves the size bound and `Adjacent.MixedCommon.reject` excludes mixed profiles. The 65 numerical intervals split the opposite representative index. Interval zero tests target class zero, with all 1,016 anchors and all ordered adjacent profiles. Its native lemma took 28 s, or 53.854 s including the dependency build (85.971 CPU s, peak RSS 2,907,984 KiB). Subsequent intervals cover sixteen consecutive classes, with seven in the final interval. The 65 complete module builds took 34.016–66.479 s individually, with a median of 46.176 s. They consumed 3,078.763 worker-seconds and 3,129.204 CPU s, including dependency builds. The maximum RSS was 2,924,060 KiB. On the 68 remaining physical unions, `Adjacent.Stage6.checkBand_sound` bounds the projected words available outside their slabs. Each branch includes or excludes one site. At its leaves, a cover by unit boxes contains at most one word of a code per box. This certifies the insufficient band size directly.

For type two, the Lean enumeration considers 16,995,062,784 ordered support descriptions, including 55,758,080 repeats due to stabilizers. The paper reports 16,939,304,704 distinct ordered pairs. For opposite class zero, generating the 755,252 allowed pairs of masks with 2,948 first masks took 25.900 s. Building the planar index took 18.864 s and scanning the first opposite class through the middle stage took 13.927 s. Checking the eight diagnostic layouts used 13 mask keys and 172 labelled entries, with 13.064 s for an atlas scan and 26.149 s for the geometry joins. Lemma 16’s retention proof applies to each chosen perfect matching. All 66 native facts compiled, covering the 64 intervals across all eight ordered gap patterns. The runs consumed 8,723.434 worker-seconds and 1,595.063 s of parallel wall time. The median chunk took 128.255 s, the longest took 295.250 s, and peak RSS was 2,538,384 KiB. The audit of `TypeTwo.Search.all_chunks` contains the three standard axioms and the 66 numerical checks. The geometric implication `TypeTwo.Search.exclude_two_of_chunks` uses only the standard three.

The paper distinguishes 21,378,687 distinct type-three pairs from 21,633,276 descriptions. An independent replay of the paper’s minimum-class search compared all 343 sites of each opposite cube and retained the first motion producing that cube. Among the 348,488 source assignments, 204,922 had nonempty six-contact lists. For each of the 1,016 opposite atlas classes, the description count equalled its stabiliser order times its number of physical pairs. The replay took 86.18 s with peak RSS 998,296 KiB.

| Opposite atlas class (zero-based) | Stabiliser | Descriptions | Distinct pairs | Repetitions |
| ---: | ---: | ---: | ---: | ---: |
| 501 | 3 | 21,531 | 7,177 | 14,354 |
| 903 | 2 | 36,406 | 18,203 | 18,203 |
| 932 | 3 | 12,804 | 4,268 | 8,536 |
| 936 | 3 | 31,599 | 10,533 | 21,066 |
| 986 | 6 | 230,916 | 38,486 | 192,430 |
| **All 1,016 classes** | | **21,633,276** | **21,378,687** | **254,589** |

The released program samples one class per group element in its coordinate-validation loop. The pinned adjacent program reruns Stage 4 on the two overlap-16 candidates supplied by Stage 3. Lean reproduced all source counts and zero surviving type-three joins. Some intermediate pair and visit counts use different symmetry reductions.

## Type-three performance decision

The stratified sample generated all 16,727,424 labelled orbit descriptions and 138,670 distinct first-cut masks. It used the 343 translations of each of 32 evenly spaced atlas representatives (10,976 sources). Of these, 411 selected query slots (0, 1). All 411 passed the production checker and the signature-filter prototype. Preprocessing the full table reached 3.88 GiB RSS in a separate sample. The reference program took 83.84 s for its full run.

| Operation on the same 411 sources | Measured CPU time | Linear estimate for 348,488 sources |
| --- | ---: | ---: |
| Six contact lookups alone | 5.23 s | 74 min |
| Cached crossing signatures and exact joins, prototype | 5.90 s | 83 min |
| Committed checker with short-circuit domain lookups and exact joins | 7.73 s | 109 min |

These estimates exclude repeated index construction. The cohort samples one of fifteen slot pairs, so the full mix can differ. The production search uses a superset of the reference program's minimum-class domain. The reference counted 87,122 phases in each of four interleaved source groups, zero surviving joins, and 5,220,670 / 5,586,310 / 5,387,317 / 5,438,979 six-contact descriptions. The unpruned description counts can differ. Charlie approved continuing at the measured cost. The complete Lean search passed all twenty native checks. Their combined CPU time was 2,635.904 s. Individual wall times ranged from 109.725 s to 246.17 s, and peak RSS was 4,743,880 KiB. Each uses all 16,727,424 labelled orbit descriptions for the opposite anchor and six transverse supports. Five query-slot parts and four residue classes of the source atlas index cover every source. In the first query-slot part the first two source residues passed in 246.17 s and 246.16 s wall time, respectively. Their CPU times were 179.15 s and 181.40 s, with peaks of 4,602,764 and 4,601,348 KiB.

Lean and an instrumented replay of the released C++ agree on all twenty counts of source assignments. The four source strips are the atlas row index modulo four.

| Query-slot part | Strip 0 | Strip 1 | Strip 2 | Strip 3 |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 17,031 | 16,673 | 16,608 | 17,089 |
| 1 | 18,433 | 18,450 | 18,380 | 17,658 |
| 2 | 18,009 | 18,175 | 17,962 | 17,457 |
| 3 | 17,254 | 17,364 | 17,564 | 18,149 |
| 4 | 16,395 | 16,460 | 16,608 | 16,769 |
| **Total** | **87,122** | **87,122** | **87,122** | **87,122** |

The normalized formulation of Lemma 18 covers every source translation and every opposite and transverse atlas image. Its caller, Proposition 17, uses `atlas_complete` and frame normalization to rule out the geometric full-band pattern for every code of every size. The audit of `TypeThree.no_join` contains the three standard axioms and twenty native checks. The audit of `TypeThree.exclude` adds exactly the twenty-four cube atlas classification checks.

## Build and axiom audit

From `seven-cycle-five/lean/` run

```sh
lake build
lake env lean scripts/axioms.lean
```

To verify the axiom allowlist and the Boolean goal type of each direct native proof, capture the output of the second command and run `python3 scripts/check_axioms.py path/to/axioms.log`. The default Lake target checks modules in dependency order. It runs one proof compiler when available memory is below 12 GiB or cannot be determined, and up to two on larger Linux machines. The adjacent front search runs on its own. Set `SEVEN_CYCLE_JOBS=1` to request a serial replay.

GitHub Actions builds `SevenCycle.Bitsets.Regression` on pull requests and pushes to `main` that change the Lean project or its CI configuration. This checks a sample atlas representative, cyclic endpoints, padding and a coordinate permutation. The full proof and axiom audit can be reproduced locally with the commands above. [CI workflow](../../.github/workflows/seven-cycle-lean.yml)

To replay one of 12 partitions of the native proof modules from a checkout, run

```sh
SEVEN_CYCLE_JOBS=1 SEVEN_CYCLE_LANE=0 SEVEN_CYCLE_LANES=12 lake build SevenCycle:nativeLane
```

A fresh local Git checkout at `37b8f6b9b5fafcd5e1d5e4ec3735b4b24f90b9f9` passed the unqualified `lake build` in **150.736 s**. Preparation of 140 native-free modules took 520.81 s. The checkout used pinned dependency artifacts and 203 native module artifacts from independent ordinary Lake compilations. The verifier checked the source and generated-output hashes of each restored module. Those modules contain all 205 direct native checks. The per-check ledger records their compilation times; the local 150.736 s measures assembly using these artifacts. The final axiom printout took 22.917 s, the strict allowlist and Boolean-goal check took 2.996 s, and the Lake hash replay took 6.407 s.

The signed-off statement blob is unchanged. The 105-word example uses a proved array checker and kernel reduction, and all six public sanity lemmas use only the standard three axioms. All requested proof obligations are closed.

The following output comes from recompiling the public caller and its proof imports at `37b8f6b`. Both public bounds use the same 197 compiler-generated native axioms and the three standard axioms. The 197 comprise 36 atlas traversal facts, 20 type-three checks, 66 type-two checks, 65 adjacent front checks and 10 physical-slab or exterior checks. The other eight native proofs verify atlas rows, their pairwise separation, their stabilisers, the gap-three cut cross-check and a final-orbit regression. The conditional five-dimensional corollary has the three standard axioms only. The strict audit covers all 231 printed declarations, including all 207 theorems under `SevenCycle/Native/`, and checks that all 205 direct native proofs conclude a Boolean equality to `true`.

```text
'SevenCycle.card_le_112' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 SevenCycle.Native.adjacent1111_slab_join._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block000._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block001._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block002._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block003._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block004._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block005._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block006._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block007._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block008._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block009._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block010._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block011._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block012._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block013._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block014._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block015._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block016._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block017._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block018._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block019._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block020._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block021._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block022._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block023._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block024._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block025._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block026._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block027._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block028._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block029._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block030._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block031._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block032._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block033._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block034._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block035._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block036._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block037._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block038._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block039._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block040._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block041._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block042._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block043._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block044._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block045._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block046._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block047._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block048._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block049._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block050._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block051._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block052._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block053._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block054._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block055._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block056._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block057._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block058._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block059._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block060._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block061._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block062._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block063._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block064._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r0_g0._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r0_g1._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r0_g2._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r0_g3._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r0_g4._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r0_g5._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r0_g6._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r0_g7._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r1_g0._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r1_g1._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r1_g2._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r1_g3._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r1_g4._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r1_g5._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r1_g6._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r1_g7._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r2_g0._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r2_g1._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r2_g2._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r2_g3._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r2_g4._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r2_g5._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r2_g6._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r2_g7._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r0_d0._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r0_d1._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r0_d2._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r0_d3._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r1_d0._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r1_d1._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r1_d2._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r1_d3._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r2_d0._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r2_d1._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r2_d2._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r2_d3._native.native_decide.ax_1_1,
 SevenCycle.Native.exterior_block0._native.native_decide.ax_1_1,
 SevenCycle.Native.exterior_block1._native.native_decide.ax_1_1,
 SevenCycle.Native.exterior_block2._native.native_decide.ax_1_1,
 SevenCycle.Native.exterior_block3._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p0_s0._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p0_s1._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p0_s2._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p0_s3._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p1_s0._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p1_s1._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p1_s2._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p1_s3._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p2_s0._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p2_s1._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p2_s2._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p2_s3._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p3_s0._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p3_s1._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p3_s2._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p3_s3._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p4_s0._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p4_s1._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p4_s2._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p4_s3._native.native_decide.ax_1_1,
 SevenCycle.Native.mixed1112_slab_join._native.native_decide.ax_1_1,
 SevenCycle.Native.mixed1122_slab_join._native.native_decide.ax_1_1,
 SevenCycle.Native.mixed1123_slab_join._native.native_decide.ax_1_1,
 SevenCycle.Native.mixedBands1122._native.native_decide.ax_1_1,
 SevenCycle.Native.mixedBands1123._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_0000._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_0001._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_0002_to_0016._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_01._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_02._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_03._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_04._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_05._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_06._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_07._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_08._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_09._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_10._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_11._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_12._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_13._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_14._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_15._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_16._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_17._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_18._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_19._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_20._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_21._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_22._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_23._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_24._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_25._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_26._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_27._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_28._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_29._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_30._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_31._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_32._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_33._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_34._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_35._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_36._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_37._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_38._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_39._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_40._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_41._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_42._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_43._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_44._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_45._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_46._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_47._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_48._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_49._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_50._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_51._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_52._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_53._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_54._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_55._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_56._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_57._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_58._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_59._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_60._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_61._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_62._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_63._native.native_decide.ax_1_1]
'SevenCycle.card_le_392' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 SevenCycle.Native.adjacent1111_slab_join._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block000._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block001._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block002._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block003._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block004._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block005._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block006._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block007._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block008._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block009._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block010._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block011._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block012._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block013._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block014._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block015._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block016._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block017._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block018._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block019._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block020._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block021._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block022._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block023._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block024._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block025._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block026._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block027._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block028._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block029._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block030._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block031._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block032._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block033._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block034._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block035._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block036._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block037._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block038._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block039._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block040._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block041._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block042._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block043._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block044._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block045._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block046._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block047._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block048._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block049._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block050._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block051._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block052._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block053._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block054._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block055._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block056._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block057._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block058._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block059._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block060._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block061._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block062._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block063._native.native_decide.ax_1_1,
 SevenCycle.Native.adjacent_block064._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r0_g0._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r0_g1._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r0_g2._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r0_g3._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r0_g4._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r0_g5._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r0_g6._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r0_g7._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r1_g0._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r1_g1._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r1_g2._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r1_g3._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r1_g4._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r1_g5._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r1_g6._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r1_g7._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r2_g0._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r2_g1._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r2_g2._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r2_g3._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r2_g4._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r2_g5._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r2_g6._native.native_decide.ax_1_1,
 SevenCycle.Native.classify33_r2_g7._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r0_d0._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r0_d1._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r0_d2._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r0_d3._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r1_d0._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r1_d1._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r1_d2._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r1_d3._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r2_d0._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r2_d1._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r2_d2._native.native_decide.ax_1_1,
 SevenCycle.Native.exclude34_r2_d3._native.native_decide.ax_1_1,
 SevenCycle.Native.exterior_block0._native.native_decide.ax_1_1,
 SevenCycle.Native.exterior_block1._native.native_decide.ax_1_1,
 SevenCycle.Native.exterior_block2._native.native_decide.ax_1_1,
 SevenCycle.Native.exterior_block3._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p0_s0._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p0_s1._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p0_s2._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p0_s3._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p1_s0._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p1_s1._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p1_s2._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p1_s3._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p2_s0._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p2_s1._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p2_s2._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p2_s3._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p3_s0._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p3_s1._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p3_s2._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p3_s3._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p4_s0._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p4_s1._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p4_s2._native.native_decide.ax_1_1,
 SevenCycle.Native.gap_three_p4_s3._native.native_decide.ax_1_1,
 SevenCycle.Native.mixed1112_slab_join._native.native_decide.ax_1_1,
 SevenCycle.Native.mixed1122_slab_join._native.native_decide.ax_1_1,
 SevenCycle.Native.mixed1123_slab_join._native.native_decide.ax_1_1,
 SevenCycle.Native.mixedBands1122._native.native_decide.ax_1_1,
 SevenCycle.Native.mixedBands1123._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_0000._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_0001._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_0002_to_0016._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_01._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_02._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_03._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_04._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_05._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_06._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_07._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_08._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_09._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_10._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_11._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_12._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_13._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_14._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_15._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_16._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_17._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_18._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_19._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_20._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_21._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_22._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_23._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_24._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_25._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_26._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_27._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_28._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_29._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_30._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_31._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_32._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_33._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_34._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_35._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_36._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_37._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_38._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_39._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_40._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_41._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_42._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_43._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_44._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_45._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_46._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_47._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_48._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_49._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_50._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_51._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_52._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_53._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_54._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_55._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_56._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_57._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_58._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_59._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_60._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_61._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_62._native.native_decide.ax_1_1,
 SevenCycle.Native.typeTwo_chunk_63._native.native_decide.ax_1_1]
'SevenCycle.Proof.five_of_four' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Native checks

The ledger gives elapsed times for individual modules or declarations. The first adjacent interval includes a dependency build, as detailed above. Each conclusion has the form `checker data = true`.

| Lemma under `SevenCycle.Native` | File under `SevenCycle/Native/` | Meaning of a successful check | Wall time |
| --- | --- | --- | ---: |
| `adjacent1111_slab_join` | `AdjacentSlabJoin.lean` | `Adjacent.SlabJoin.checkFrames_sound` proves that every compatible union of the supplied framed slabs reaches the checked exterior table. | 27 s |
| `mixed1112_slab_join` | `MixedSlabJoins.lean` | `MixedSlabs.three_sound` excludes every compatible ordered triple of physical slabs for 1112. | 3.096 s (declaration) |
| `mixed1122_slab_join` | `MixedSlabJoins.lean` | `MixedSlabs.two_sound` places every compatible 1122 pair in the four-row union table. | 0.570 s (declaration) |
| `mixed1123_slab_join` | `MixedSlabJoins.lean` | `MixedSlabs.two_sound` places every compatible 1123 pair in the 64-row union table. | 2.424 s (declaration) |
| `mixedBands1122` | `MixedBands1122.lean` | `Stage6.rowsCheck_sound` proves that each of four physical unions has an impossible marked band. | 5.3 s |
| `mixedBands1123` | `MixedBands1123.lean` | `Stage6.rowsCheck_sound` proves that each of 64 physical unions has an impossible marked band. | 35 s |
| `adjacent_block000` | `Adjacent/Block000.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [0, 1) over every source class and ordered adjacent profile. | 53.854 s |
| `adjacent_block001` | `Adjacent/Block001.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [1, 17) over every source class and ordered adjacent profile. | 39.996 s |
| `adjacent_block002` | `Adjacent/Block002.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [17, 33) over every source class and ordered adjacent profile. | 46.176 s |
| `adjacent_block003` | `Adjacent/Block003.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [33, 49) over every source class and ordered adjacent profile. | 51.129 s |
| `adjacent_block004` | `Adjacent/Block004.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [49, 65) over every source class and ordered adjacent profile. | 53.703 s |
| `adjacent_block005` | `Adjacent/Block005.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [65, 81) over every source class and ordered adjacent profile. | 44.69 s |
| `adjacent_block006` | `Adjacent/Block006.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [81, 97) over every source class and ordered adjacent profile. | 40.477 s |
| `adjacent_block007` | `Adjacent/Block007.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [97, 113) over every source class and ordered adjacent profile. | 54.341 s |
| `adjacent_block008` | `Adjacent/Block008.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [113, 129) over every source class and ordered adjacent profile. | 51.801 s |
| `adjacent_block009` | `Adjacent/Block009.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [129, 145) over every source class and ordered adjacent profile. | 47.791 s |
| `adjacent_block010` | `Adjacent/Block010.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [145, 161) over every source class and ordered adjacent profile. | 49.666 s |
| `adjacent_block011` | `Adjacent/Block011.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [161, 177) over every source class and ordered adjacent profile. | 48.422 s |
| `adjacent_block012` | `Adjacent/Block012.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [177, 193) over every source class and ordered adjacent profile. | 43.215 s |
| `adjacent_block013` | `Adjacent/Block013.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [193, 209) over every source class and ordered adjacent profile. | 47.02 s |
| `adjacent_block014` | `Adjacent/Block014.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [209, 225) over every source class and ordered adjacent profile. | 43.119 s |
| `adjacent_block015` | `Adjacent/Block015.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [225, 241) over every source class and ordered adjacent profile. | 43.856 s |
| `adjacent_block016` | `Adjacent/Block016.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [241, 257) over every source class and ordered adjacent profile. | 46.541 s |
| `adjacent_block017` | `Adjacent/Block017.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [257, 273) over every source class and ordered adjacent profile. | 53.321 s |
| `adjacent_block018` | `Adjacent/Block018.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [273, 289) over every source class and ordered adjacent profile. | 44.401 s |
| `adjacent_block019` | `Adjacent/Block019.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [289, 305) over every source class and ordered adjacent profile. | 42.894 s |
| `adjacent_block020` | `Adjacent/Block020.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [305, 321) over every source class and ordered adjacent profile. | 60.113 s |
| `adjacent_block021` | `Adjacent/Block021.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [321, 337) over every source class and ordered adjacent profile. | 44.981 s |
| `adjacent_block022` | `Adjacent/Block022.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [337, 353) over every source class and ordered adjacent profile. | 46.032 s |
| `adjacent_block023` | `Adjacent/Block023.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [353, 369) over every source class and ordered adjacent profile. | 43.216 s |
| `adjacent_block024` | `Adjacent/Block024.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [369, 385) over every source class and ordered adjacent profile. | 45.482 s |
| `adjacent_block025` | `Adjacent/Block025.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [385, 401) over every source class and ordered adjacent profile. | 52.574 s |
| `adjacent_block026` | `Adjacent/Block026.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [401, 417) over every source class and ordered adjacent profile. | 66.479 s |
| `adjacent_block027` | `Adjacent/Block027.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [417, 433) over every source class and ordered adjacent profile. | 46.507 s |
| `adjacent_block028` | `Adjacent/Block028.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [433, 449) over every source class and ordered adjacent profile. | 42.519 s |
| `adjacent_block029` | `Adjacent/Block029.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [449, 465) over every source class and ordered adjacent profile. | 48.147 s |
| `adjacent_block030` | `Adjacent/Block030.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [465, 481) over every source class and ordered adjacent profile. | 53.306 s |
| `adjacent_block031` | `Adjacent/Block031.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [481, 497) over every source class and ordered adjacent profile. | 46.029 s |
| `adjacent_block032` | `Adjacent/Block032.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [497, 513) over every source class and ordered adjacent profile. | 56.392 s |
| `adjacent_block033` | `Adjacent/Block033.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [513, 529) over every source class and ordered adjacent profile. | 44.49 s |
| `adjacent_block034` | `Adjacent/Block034.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [529, 545) over every source class and ordered adjacent profile. | 47.738 s |
| `adjacent_block035` | `Adjacent/Block035.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [545, 561) over every source class and ordered adjacent profile. | 49.797 s |
| `adjacent_block036` | `Adjacent/Block036.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [561, 577) over every source class and ordered adjacent profile. | 45.719 s |
| `adjacent_block037` | `Adjacent/Block037.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [577, 593) over every source class and ordered adjacent profile. | 45.133 s |
| `adjacent_block038` | `Adjacent/Block038.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [593, 609) over every source class and ordered adjacent profile. | 54.516 s |
| `adjacent_block039` | `Adjacent/Block039.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [609, 625) over every source class and ordered adjacent profile. | 44.797 s |
| `adjacent_block040` | `Adjacent/Block040.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [625, 641) over every source class and ordered adjacent profile. | 47.2 s |
| `adjacent_block041` | `Adjacent/Block041.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [641, 657) over every source class and ordered adjacent profile. | 41.824 s |
| `adjacent_block042` | `Adjacent/Block042.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [657, 673) over every source class and ordered adjacent profile. | 45.661 s |
| `adjacent_block043` | `Adjacent/Block043.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [673, 689) over every source class and ordered adjacent profile. | 53.292 s |
| `adjacent_block044` | `Adjacent/Block044.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [689, 705) over every source class and ordered adjacent profile. | 41.669 s |
| `adjacent_block045` | `Adjacent/Block045.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [705, 721) over every source class and ordered adjacent profile. | 49.543 s |
| `adjacent_block046` | `Adjacent/Block046.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [721, 737) over every source class and ordered adjacent profile. | 44.271 s |
| `adjacent_block047` | `Adjacent/Block047.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [737, 753) over every source class and ordered adjacent profile. | 48.191 s |
| `adjacent_block048` | `Adjacent/Block048.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [753, 769) over every source class and ordered adjacent profile. | 46.209 s |
| `adjacent_block049` | `Adjacent/Block049.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [769, 785) over every source class and ordered adjacent profile. | 51.079 s |
| `adjacent_block050` | `Adjacent/Block050.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [785, 801) over every source class and ordered adjacent profile. | 45.685 s |
| `adjacent_block051` | `Adjacent/Block051.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [801, 817) over every source class and ordered adjacent profile. | 43.627 s |
| `adjacent_block052` | `Adjacent/Block052.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [817, 833) over every source class and ordered adjacent profile. | 59.499 s |
| `adjacent_block053` | `Adjacent/Block053.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [833, 849) over every source class and ordered adjacent profile. | 43.41 s |
| `adjacent_block054` | `Adjacent/Block054.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [849, 865) over every source class and ordered adjacent profile. | 48.124 s |
| `adjacent_block055` | `Adjacent/Block055.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [865, 881) over every source class and ordered adjacent profile. | 47.425 s |
| `adjacent_block056` | `Adjacent/Block056.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [881, 897) over every source class and ordered adjacent profile. | 39.973 s |
| `adjacent_block057` | `Adjacent/Block057.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [897, 913) over every source class and ordered adjacent profile. | 44.372 s |
| `adjacent_block058` | `Adjacent/Block058.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [913, 929) over every source class and ordered adjacent profile. | 41.777 s |
| `adjacent_block059` | `Adjacent/Block059.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [929, 945) over every source class and ordered adjacent profile. | 40.914 s |
| `adjacent_block060` | `Adjacent/Block060.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [945, 961) over every source class and ordered adjacent profile. | 49.703 s |
| `adjacent_block061` | `Adjacent/Block061.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [961, 977) over every source class and ordered adjacent profile. | 44.856 s |
| `adjacent_block062` | `Adjacent/Block062.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [977, 993) over every source class and ordered adjacent profile. | 40.253 s |
| `adjacent_block063` | `Adjacent/Block063.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [993, 1009) over every source class and ordered adjacent profile. | 55.81 s |
| `adjacent_block064` | `Adjacent/Block064.lean` | `Adjacent.FrontSearch.of_ranges` and `anchor_of_run` retain actual anchored slabs for opposite classes [1009, 1016) over every source class and ordered adjacent profile. | 34.016 s |
| `gap_three_p0_s0` | `GapThree/P0S0.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 0 and source class index 0 modulo four using the full orbit table. | 246.17 s |
| `gap_three_p0_s1` | `GapThree/P0S1.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 0 and source class index 1 modulo four using the full orbit table. | 246.16 s |
| `gap_three_p0_s2` | `GapThree/P0S2.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 0 and source class index 2 modulo four using the full orbit table. | 149.156 s |
| `gap_three_p0_s3` | `GapThree/P0S3.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 0 and source class index 3 modulo four using the full orbit table. | 140.474 s |
| `gap_three_p1_s0` | `GapThree/P1S0.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 1 and source class index 0 modulo four using the full orbit table. | 123.423 s |
| `gap_three_p1_s1` | `GapThree/P1S1.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 1 and source class index 1 modulo four using the full orbit table. | 141.752 s |
| `gap_three_p1_s2` | `GapThree/P1S2.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 1 and source class index 2 modulo four using the full orbit table. | 126.985 s |
| `gap_three_p1_s3` | `GapThree/P1S3.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 1 and source class index 3 modulo four using the full orbit table. | 126.021 s |
| `gap_three_p2_s0` | `GapThree/P2S0.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 2 and source class index 0 modulo four using the full orbit table. | 122.52 s |
| `gap_three_p2_s1` | `GapThree/P2S1.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 2 and source class index 1 modulo four using the full orbit table. | 129.776 s |
| `gap_three_p2_s2` | `GapThree/P2S2.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 2 and source class index 2 modulo four using the full orbit table. | 113.309 s |
| `gap_three_p2_s3` | `GapThree/P2S3.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 2 and source class index 3 modulo four using the full orbit table. | 109.725 s |
| `gap_three_p3_s0` | `GapThree/P3S0.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 3 and source class index 0 modulo four using the full orbit table. | 135.279 s |
| `gap_three_p3_s1` | `GapThree/P3S1.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 3 and source class index 1 modulo four using the full orbit table. | 124.873 s |
| `gap_three_p3_s2` | `GapThree/P3S2.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 3 and source class index 2 modulo four using the full orbit table. | 128.819 s |
| `gap_three_p3_s3` | `GapThree/P3S3.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 3 and source class index 3 modulo four using the full orbit table. | 131.25 s |
| `gap_three_p4_s0` | `GapThree/P4S0.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 4 and source class index 0 modulo four using the full orbit table. | 121.744 s |
| `gap_three_p4_s1` | `GapThree/P4S1.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 4 and source class index 1 modulo four using the full orbit table. | 117.79 s |
| `gap_three_p4_s2` | `GapThree/P4S2.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 4 and source class index 2 modulo four using the full orbit table. | 111.254 s |
| `gap_three_p4_s3` | `GapThree/P4S3.lean` | `TypeThree.checkShard_sound` excludes every six-way join for query-slot part 4 and source class index 3 modulo four using the full orbit table. | 115.054 s |
| `typeTwo_0002_to_0016` | `TypeTwo/Chunk00.lean` | `TypeTwo.Search.fastCheck_sound` excludes a surviving layout for opposite classes 2–15 against all source representatives and eight distance assignments. | 102.556 s |
| `typeTwo_chunk_01` | `TypeTwo/Chunk01.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 16–31 against all source representatives and eight distance assignments. | 122.636 s |
| `typeTwo_chunk_02` | `TypeTwo/Chunk02.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 32–47 against all source representatives and eight distance assignments. | 144.249 s |
| `typeTwo_chunk_03` | `TypeTwo/Chunk03.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 48–63 against all source representatives and eight distance assignments. | 141.078 s |
| `typeTwo_chunk_04` | `TypeTwo/Chunk04.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 64–79 against all source representatives and eight distance assignments. | 108.172 s |
| `typeTwo_chunk_05` | `TypeTwo/Chunk05.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 80–95 against all source representatives and eight distance assignments. | 63.251 s |
| `typeTwo_chunk_06` | `TypeTwo/Chunk06.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 96–111 against all source representatives and eight distance assignments. | 133.031 s |
| `typeTwo_chunk_07` | `TypeTwo/Chunk07.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 112–127 against all source representatives and eight distance assignments. | 295.25 s |
| `typeTwo_chunk_08` | `TypeTwo/Chunk08.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 128–143 against all source representatives and eight distance assignments. | 135.322 s |
| `typeTwo_chunk_09` | `TypeTwo/Chunk09.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 144–159 against all source representatives and eight distance assignments. | 169.084 s |
| `typeTwo_chunk_10` | `TypeTwo/Chunk10.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 160–175 against all source representatives and eight distance assignments. | 193.55 s |
| `typeTwo_chunk_11` | `TypeTwo/Chunk11.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 176–191 against all source representatives and eight distance assignments. | 121.633 s |
| `typeTwo_chunk_12` | `TypeTwo/Chunk12.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 192–207 against all source representatives and eight distance assignments. | 110.951 s |
| `typeTwo_chunk_13` | `TypeTwo/Chunk13.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 208–223 against all source representatives and eight distance assignments. | 122.494 s |
| `typeTwo_chunk_14` | `TypeTwo/Chunk14.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 224–239 against all source representatives and eight distance assignments. | 186.346 s |
| `typeTwo_chunk_15` | `TypeTwo/Chunk15.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 240–255 against all source representatives and eight distance assignments. | 118.699 s |
| `typeTwo_chunk_16` | `TypeTwo/Chunk16.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 256–271 against all source representatives and eight distance assignments. | 118.856 s |
| `typeTwo_chunk_17` | `TypeTwo/Chunk17.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 272–287 against all source representatives and eight distance assignments. | 125.628 s |
| `typeTwo_chunk_18` | `TypeTwo/Chunk18.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 288–303 against all source representatives and eight distance assignments. | 128.126 s |
| `typeTwo_chunk_19` | `TypeTwo/Chunk19.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 304–319 against all source representatives and eight distance assignments. | 166.623 s |
| `typeTwo_chunk_20` | `TypeTwo/Chunk20.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 320–335 against all source representatives and eight distance assignments. | 158.319 s |
| `typeTwo_chunk_21` | `TypeTwo/Chunk21.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 336–351 against all source representatives and eight distance assignments. | 168.894 s |
| `typeTwo_chunk_22` | `TypeTwo/Chunk22.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 352–367 against all source representatives and eight distance assignments. | 112.957 s |
| `typeTwo_chunk_23` | `TypeTwo/Chunk23.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 368–383 against all source representatives and eight distance assignments. | 135.212 s |
| `typeTwo_chunk_24` | `TypeTwo/Chunk24.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 384–399 against all source representatives and eight distance assignments. | 102.597 s |
| `typeTwo_chunk_25` | `TypeTwo/Chunk25.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 400–415 against all source representatives and eight distance assignments. | 132.644 s |
| `typeTwo_chunk_26` | `TypeTwo/Chunk26.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 416–431 against all source representatives and eight distance assignments. | 122.48 s |
| `typeTwo_chunk_27` | `TypeTwo/Chunk27.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 432–447 against all source representatives and eight distance assignments. | 110.707 s |
| `typeTwo_chunk_28` | `TypeTwo/Chunk28.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 448–463 against all source representatives and eight distance assignments. | 150.169 s |
| `typeTwo_chunk_29` | `TypeTwo/Chunk29.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 464–479 against all source representatives and eight distance assignments. | 168.041 s |
| `typeTwo_chunk_30` | `TypeTwo/Chunk30.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 480–495 against all source representatives and eight distance assignments. | 144.338 s |
| `typeTwo_chunk_31` | `TypeTwo/Chunk31.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 496–511 against all source representatives and eight distance assignments. | 176.264 s |
| `typeTwo_chunk_32` | `TypeTwo/Chunk32.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 512–527 against all source representatives and eight distance assignments. | 152.314 s |
| `typeTwo_chunk_33` | `TypeTwo/Chunk33.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 528–543 against all source representatives and eight distance assignments. | 158.836 s |
| `typeTwo_chunk_34` | `TypeTwo/Chunk34.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 544–559 against all source representatives and eight distance assignments. | 116.821 s |
| `typeTwo_chunk_35` | `TypeTwo/Chunk35.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 560–575 against all source representatives and eight distance assignments. | 138.984 s |
| `typeTwo_chunk_36` | `TypeTwo/Chunk36.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 576–591 against all source representatives and eight distance assignments. | 149.025 s |
| `typeTwo_chunk_37` | `TypeTwo/Chunk37.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 592–607 against all source representatives and eight distance assignments. | 128.384 s |
| `typeTwo_chunk_38` | `TypeTwo/Chunk38.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 608–623 against all source representatives and eight distance assignments. | 97.918 s |
| `typeTwo_chunk_39` | `TypeTwo/Chunk39.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 624–639 against all source representatives and eight distance assignments. | 96.662 s |
| `typeTwo_chunk_40` | `TypeTwo/Chunk40.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 640–655 against all source representatives and eight distance assignments. | 95.166 s |
| `typeTwo_chunk_41` | `TypeTwo/Chunk41.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 656–671 against all source representatives and eight distance assignments. | 181.214 s |
| `typeTwo_chunk_42` | `TypeTwo/Chunk42.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 672–687 against all source representatives and eight distance assignments. | 154.309 s |
| `typeTwo_chunk_43` | `TypeTwo/Chunk43.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 688–703 against all source representatives and eight distance assignments. | 111.642 s |
| `typeTwo_chunk_44` | `TypeTwo/Chunk44.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 704–719 against all source representatives and eight distance assignments. | 144.757 s |
| `typeTwo_chunk_45` | `TypeTwo/Chunk45.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 720–735 against all source representatives and eight distance assignments. | 113.293 s |
| `typeTwo_chunk_46` | `TypeTwo/Chunk46.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 736–751 against all source representatives and eight distance assignments. | 122.484 s |
| `typeTwo_chunk_47` | `TypeTwo/Chunk47.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 752–767 against all source representatives and eight distance assignments. | 148.198 s |
| `typeTwo_chunk_48` | `TypeTwo/Chunk48.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 768–783 against all source representatives and eight distance assignments. | 126.078 s |
| `typeTwo_chunk_49` | `TypeTwo/Chunk49.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 784–799 against all source representatives and eight distance assignments. | 129.147 s |
| `typeTwo_chunk_50` | `TypeTwo/Chunk50.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 800–815 against all source representatives and eight distance assignments. | 110.115 s |
| `typeTwo_chunk_51` | `TypeTwo/Chunk51.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 816–831 against all source representatives and eight distance assignments. | 130.327 s |
| `typeTwo_chunk_52` | `TypeTwo/Chunk52.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 832–847 against all source representatives and eight distance assignments. | 125.317 s |
| `typeTwo_chunk_53` | `TypeTwo/Chunk53.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 848–863 against all source representatives and eight distance assignments. | 112.152 s |
| `typeTwo_chunk_54` | `TypeTwo/Chunk54.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 864–879 against all source representatives and eight distance assignments. | 117.952 s |
| `typeTwo_chunk_55` | `TypeTwo/Chunk55.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 880–895 against all source representatives and eight distance assignments. | 113.895 s |
| `typeTwo_chunk_56` | `TypeTwo/Chunk56.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 896–911 against all source representatives and eight distance assignments. | 82.386 s |
| `typeTwo_chunk_57` | `TypeTwo/Chunk57.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 912–927 against all source representatives and eight distance assignments. | 145.688 s |
| `typeTwo_chunk_58` | `TypeTwo/Chunk58.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 928–943 against all source representatives and eight distance assignments. | 91.507 s |
| `typeTwo_chunk_59` | `TypeTwo/Chunk59.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 944–959 against all source representatives and eight distance assignments. | 243.212 s |
| `typeTwo_chunk_60` | `TypeTwo/Chunk60.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 960–975 against all source representatives and eight distance assignments. | 172.378 s |
| `typeTwo_chunk_61` | `TypeTwo/Chunk61.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 976–991 against all source representatives and eight distance assignments. | 103.723 s |
| `typeTwo_chunk_62` | `TypeTwo/Chunk62.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 992–1007 against all source representatives and eight distance assignments. | 142.2 s |
| `typeTwo_chunk_63` | `TypeTwo/Chunk63.lean` | `TypeTwo.Search.chunk_sound` excludes a surviving layout for opposite classes 1008–1015 against all source representatives and eight distance assignments. | 68.851 s |
| `typeTwo_0000` | `TypeTwo/R0000.lean` | `TypeTwo.Search.check_sound` excludes a surviving layout for opposite class 0 against all source representatives and eight distance assignments. | 66.923 s |
| `typeTwo_0001` | `TypeTwo/R0001.lean` | `TypeTwo.Search.check_sound` excludes a surviving layout for opposite class 1 against all source representatives and eight distance assignments. | 41.419 s |
| `atlas_rows_checked` | `AtlasRows.lean` | `Atlas.rowsValid_sound` proves size 33 and pairwise separation for every decoded row. | 5.9 s |
| `atlas_energies_checked` | `OrbitSeparation.lean` | `Atlas.Invariants.energiesDistinct_sound` shows two valid input rows related by an isometry must have the same index. | 11 s |
| `atlas_gap_three_cuts` | `GapThreeCuts.lean` | `TypeThree.cutsDistinct_sound` separates the decoded cuts at gap three on every axis of every input representative. | 4.56 s |
| `exterior_block0` | `Exterior/Block0.lean` | `Adjacent.UnionTable.windowCheck_sound` bounds all code extensions of input union rows 0–443 by verifying a blocker or a clique-cover box at each outside site. | 35 s |
| `exterior_block1` | `Exterior/Block1.lean` | `Adjacent.UnionTable.windowCheck_sound` bounds all code extensions of input union rows 444–887 by verifying a blocker or a clique-cover box at each outside site. | 37 s |
| `exterior_block2` | `Exterior/Block2.lean` | `Adjacent.UnionTable.windowCheck_sound` bounds all code extensions of input union rows 888–1331 by verifying a blocker or a clique-cover box at each outside site. | 39 s |
| `exterior_block3` | `Exterior/Block3.lean` | `Adjacent.UnionTable.windowCheck_sound` bounds all code extensions of input union rows 1332–1775 by verifying a blocker or a clique-cover box at each outside site. | 46 s |
| `gap_three_final_orbit` | `GapThreeFinalOrbit.lean` | `TypeThree.checkBlock_sound` and `fastCutsOf_eq` exclude any normalised code whose anchor and seven other bands all come from class 1015, testing 343 translations and 16,464 labelled motions. | 52.09 s |
| `exclude34_r0_d0` | `Exclude34/R0D0.lean` | `Atlas.CubePlanes.exclude34Check_sound` excludes 34-word inputs with first plane-pair representative 0 and deficit pattern 0. | 70 s |
| `exclude34_r0_d1` | `Exclude34/R0D1.lean` | `Atlas.CubePlanes.exclude34Check_sound` excludes 34-word inputs with first plane-pair representative 0 and deficit pattern 1. | 33.47 s |
| `exclude34_r0_d2` | `Exclude34/R0D2.lean` | `Atlas.CubePlanes.exclude34Check_sound` excludes 34-word inputs with first plane-pair representative 0 and deficit pattern 2. | 23.78 s |
| `exclude34_r0_d3` | `Exclude34/R0D3.lean` | `Atlas.CubePlanes.exclude34Check_sound` excludes 34-word inputs with first plane-pair representative 0 and deficit pattern 3. | 15.17 s |
| `exclude34_r1_d0` | `Exclude34/R1D0.lean` | `Atlas.CubePlanes.exclude34Check_sound` excludes 34-word inputs with first plane-pair representative 1 and deficit pattern 0. | 42.54 s |
| `exclude34_r1_d1` | `Exclude34/R1D1.lean` | `Atlas.CubePlanes.exclude34Check_sound` excludes 34-word inputs with first plane-pair representative 1 and deficit pattern 1. | 29.75 s |
| `exclude34_r1_d2` | `Exclude34/R1D2.lean` | `Atlas.CubePlanes.exclude34Check_sound` excludes 34-word inputs with first plane-pair representative 1 and deficit pattern 2. | 41.98 s |
| `exclude34_r1_d3` | `Exclude34/R1D3.lean` | `Atlas.CubePlanes.exclude34Check_sound` excludes 34-word inputs with first plane-pair representative 1 and deficit pattern 3. | 44.6 s |
| `exclude34_r2_d0` | `Exclude34/R2D0.lean` | `Atlas.CubePlanes.exclude34Check_sound` excludes 34-word inputs with first plane-pair representative 2 and deficit pattern 0. | 107.71 s |
| `exclude34_r2_d1` | `Exclude34/R2D1.lean` | `Atlas.CubePlanes.exclude34Check_sound` excludes 34-word inputs with first plane-pair representative 2 and deficit pattern 1. | 35.19 s |
| `exclude34_r2_d2` | `Exclude34/R2D2.lean` | `Atlas.CubePlanes.exclude34Check_sound` excludes 34-word inputs with first plane-pair representative 2 and deficit pattern 2. | 21.14 s |
| `exclude34_r2_d3` | `Exclude34/R2D3.lean` | `Atlas.CubePlanes.exclude34Check_sound` excludes 34-word inputs with first plane-pair representative 2 and deficit pattern 3. | 20.66 s |
| `classify33_r0_g0` | `Census33/R0G0.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 0, patterns 0–1, to cube orbits. | 22.27 s |
| `classify33_r0_g1` | `Census33/R0G1.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 0, patterns 2, to cube orbits. | 53.85 s |
| `classify33_r0_g2` | `Census33/R0G2.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 0, patterns 3, to cube orbits. | 48.17 s |
| `classify33_r0_g3` | `Census33/R0G3.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 0, patterns 4, to cube orbits. | 28.11 s |
| `classify33_r0_g4` | `Census33/R0G4.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 0, patterns 5–9, to cube orbits. | 28.03 s |
| `classify33_r0_g5` | `Census33/R0G5.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 0, patterns 10–14, to cube orbits. | 24.34 s |
| `classify33_r0_g6` | `Census33/R0G6.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 0, patterns 15–21, to cube orbits. | 28.41 s |
| `classify33_r0_g7` | `Census33/R0G7.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 0, patterns 22–29, to cube orbits. | 14.96 s |
| `classify33_r1_g0` | `Census33/R1G0.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 1, patterns 0–1, to cube orbits. | 42.04 s |
| `classify33_r1_g1` | `Census33/R1G1.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 1, patterns 2, to cube orbits. | 22.34 s |
| `classify33_r1_g2` | `Census33/R1G2.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 1, patterns 3, to cube orbits. | 23.92 s |
| `classify33_r1_g3` | `Census33/R1G3.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 1, patterns 4, to cube orbits. | 18.40 s |
| `classify33_r1_g4` | `Census33/R1G4.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 1, patterns 5–9, to cube orbits. | 20.65 s |
| `classify33_r1_g5` | `Census33/R1G5.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 1, patterns 10–14, to cube orbits. | 20.56 s |
| `classify33_r1_g6` | `Census33/R1G6.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 1, patterns 15–21, to cube orbits. | 19.93 s |
| `classify33_r1_g7` | `Census33/R1G7.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 1, patterns 22–29, to cube orbits. | 12.08 s |
| `classify33_r2_g0` | `Census33/R2G0.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 2, patterns 0–1, to cube orbits. | 23.09 s |
| `classify33_r2_g1` | `Census33/R2G1.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 2, patterns 2, to cube orbits. | 64.80 s |
| `classify33_r2_g2` | `Census33/R2G2.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 2, patterns 3, to cube orbits. | 59.49 s |
| `classify33_r2_g3` | `Census33/R2G3.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 2, patterns 4, to cube orbits. | 23.82 s |
| `classify33_r2_g4` | `Census33/R2G4.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 2, patterns 5–9, to cube orbits. | 25.62 s |
| `classify33_r2_g5` | `Census33/R2G5.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 2, patterns 10–14, to cube orbits. | 24.01 s |
| `classify33_r2_g6` | `Census33/R2G6.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 2, patterns 15–21, to cube orbits. | 27.54 s |
| `classify33_r2_g7` | `Census33/R2G7.lean` | `Atlas.atlas_complete_of_jobs` transports the verified classification of leaves for planar representative 2, patterns 22–29, to cube orbits. | 15.85 s |
| `stabilizers_block0` | `Stabilizers/Block0.lean` | `Atlas.Stabilizers.blockCheck_sound` checks orders of rows 0–253 by testing every isometry. | 57 s |
| `stabilizers_block1` | `Stabilizers/Block1.lean` | Same checker for rows 254–507. | 58 s |
| `stabilizers_block2` | `Stabilizers/Block2.lean` | Same checker for rows 508–761. | 58 s |
| `stabilizers_block3` | `Stabilizers/Block3.lean` | Same checker for rows 762–1015. | 58 s |

For the planar orbit traversal, a full kernel attempt reached 8,212,236 KiB RSS after 38.73 s. The original native traversal took 8.2 s. The kernel-only classification in `Atlas.Planar.Kernel.atlas_two` completed in 7.4 s and also proves the original Boolean checker result. Its compatibility alias `Native.planar_classification` uses only the standard three axioms. On this Lean release the audit shows an axiom specific to each `native_decide` declaration.

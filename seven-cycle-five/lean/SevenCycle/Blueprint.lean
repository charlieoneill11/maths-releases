import SevenCycle.Adjacent.CertifiedFront
import SevenCycle.Adjacent.Exclusion
import SevenCycle.TypeTwo.Certified
import SevenCycle.TypeThree.Result
import SevenCycle.Atlas.StabilizerCensus
import SevenCycle.Native.OrbitSeparation
import SevenCycle.Adjacent.Slabs
import SevenCycle.Proof.Profiles
import SevenCycle.TypeTwo.FaceMatching
import SevenCycle.Atlas.PlanarKernel
import SevenCycle.TypeTwo.Retention
import SevenCycle.Adjacent.Retention
import SevenCycle.Atlas.SmallBounds
import SevenCycle.Atlas.Bound34
import SevenCycle.Atlas.Census33
import SevenCycle.Native.AtlasRows
import SevenCycle.Proof.Crossings
import SevenCycle.Proof.Deficits
import SevenCycle.Proof.Matching
import SevenCycle.Proof.Symmetry
import SevenCycle.Blueprint.Definitions
import SevenCycle.Proof.Bands

/-!
# Blueprint for the seven-cycle proof

These are proof obligations. They use the coordinate relation underlying the
public statement, so the finished proofs can be imported by that statement.
-/

namespace SevenCycle.Blueprint

local notation "Word" => Proof.Tuple
local notation "IsCode" => Proof.packing Proof.cycleStep
local notation "Confusable" => Proof.conflict Proof.cycleStep

theorem act_confusable {n : ℕ} (g : Isometry n) (x y : Word n) :
    Confusable (act g x) (act g y) ↔ Confusable x y :=
  Proof.Symmetry.act_confusable g x y

theorem isometry_orders :
    Fintype.card (Isometry 2) = 392 ∧ Fintype.card (Isometry 3) = 16464 :=
  Proof.Symmetry.isometry_orders

/-- Lemma 3, including the two conclusions used to bound a projected band. -/
theorem band_projection {n : ℕ} {C : Finset (Word (n+1))} (hc : IsCode C)
    (k : Fin (n+1)) (i : ZMod 7) :
    Set.InjOn (dropCoord k) (band C k i : Set (Word (n+1))) ∧
      IsCode ((band C k i).image (dropCoord k)) :=
  Bands.band_projection hc k i

theorem band_card {n : ℕ} (C : Finset (Word (n+1))) (k : Fin (n+1)) (i : ZMod 7) :
    (band C k i).card = (level C k i).card + (level C k (i+1)).card :=
  Bands.band_card C k i

theorem sum_band_card {n : ℕ} (C : Finset (Word (n+1))) (k : Fin (n+1)) :
    ∑ i : ZMod 7, (band C k i).card = 2 * C.card :=
  Bands.sum_band_card C k

theorem alternating_band_sum {n : ℕ} (C : Finset (Word (n+1))) (k : Fin (n+1))
    (i : ZMod 7) : 2 * ((level C k i).card : ℤ) =
      ∑ j : Fin 7, (-1 : ℤ) ^ j.val * ((band C k (i + (j.val : ZMod 7))).card : ℤ) :=
  Bands.alternating_band_sum C k i

theorem band_bound {n a : ℕ} (ha : ∀ D : Finset (Word n), IsCode D → D.card ≤ a)
    (C : Finset (Word (n+1))) (hc : IsCode C) : C.card ≤ 7 * a / 2 :=
  Bands.band_bound ha C hc

section Deficits

variable (h3 : ∀ D : Finset (Word 3), IsCode D → D.card ≤ 33)
variable (C : Finset (Word 4)) (hc : IsCode C) (h113 : C.card = 113)

include h3 hc h113 in
theorem deficit_sum (k : Fin 4) : ∑ i : ZMod 7, deficit C k i = 5 :=
  SevenCycle.Deficits.deficit_sum h3 C hc h113 k

include h3 hc h113 in
theorem level_from_deficits (k : Fin 4) (i : ZMod 7) :
    (level C k i).card = 14 + deficit C k (i+1) + deficit C k (i+3) + deficit C k (i+5) :=
  SevenCycle.Deficits.level_from_deficits h3 C hc h113 k i

include h3 hc h113 in
theorem deficits_one (k : Fin 4) : 2 ≤ (fullStarts C k).card ∧
    ∀ i, 14 ≤ (level C k i).card ∧ (level C k i).card ≤ 19 :=
  SevenCycle.Deficits.deficits_one h3 C hc h113 k

include h3 hc h113 in
theorem deficits_two (k : Fin 4) (h : ∃ i ∈ fullStarts C k, i+1 ∈ fullStarts C k) :
    ∃ c, HasCentre C k c :=
  SevenCycle.Deficits.deficits_two h3 C hc h113 k h

include h3 hc h113 in
theorem deficits_three (k : Fin 4) (h : ∀ i ∈ fullStarts C k, i+1 ∉ fullStarts C k)
    (h0 : 0 ∈ fullStarts C k) (h2 : 2 ∈ fullStarts C k) : 31 ≤ (band C k 1).card :=
  SevenCycle.Deficits.deficits_three h3 C hc h113 k h h0 h2

include h3 hc h113 in
theorem profile_exists : ∃ p, HasProfile C p :=
  SevenCycle.Deficits.profile_exists h3 C hc h113

end Deficits
theorem card_le_ten (C : Finset (Word 2)) (hC : IsCode C) : C.card ≤ 10 :=
  Atlas.card_le_ten C hC

/-- Lemma 6. The three displayed representatives exhaust the maximum codes. -/
theorem atlas_two (C : Finset (Word 2)) :
    (IsCode C ∧ C.card = 10) ↔
      ∃ r : Fin 3, ∃ g : Isometry 2, C = actOnCode g (twoRepresentatives r) :=
  Atlas.Planar.Kernel.atlas_two C

theorem card_le_thirty_three (C : Finset (Word 3)) (hC : IsCode C) : C.card ≤ 33 :=
  Atlas.card_le_thirty_three C hC

/-- Theorem 7. Every 33-word code is an isometric image of an actual input row. -/
theorem atlas_complete (C : Finset (Word 3)) (hC : IsCode C) (hsize : C.card = 33) :
    ∃ r : Fin atlasPlanes.size, ∃ g : Isometry 3, C = actOnCode g (atlasRepresentative r) :=
  Atlas.atlas_complete C hC hsize

theorem atlas_row_valid (r : Fin atlasPlanes.size) :
    IsCode (atlasRepresentative r) ∧ (atlasRepresentative r).card = 33 :=
  Atlas.rowsValid_sound _ Native.atlas_rows_checked r

theorem atlas_rows_inequivalent (r s : Fin atlasPlanes.size) (g : Isometry 3)
    (heq : actOnCode g (atlasRepresentative r) = atlasRepresentative s) : r = s :=
  Atlas.Invariants.energiesDistinct_sound _ Native.atlas_energies_checked Native.atlas_rows_checked r s g heq

theorem atlas_stabilizers :
    let count := fun j : ℕ => (Finset.univ.filter fun r => stabilizerOrder r = j).card
    atlasPlanes.size = 1016 ∧ count 1 = 1011 ∧ count 2 = 1 ∧ count 3 = 3 ∧ count 6 = 1 :=
  Atlas.Stabilizers.census

/-- Lemma 8. The equations on m and m' give the positions of the surviving
axes after deleting k and l respectively. The final images keep their original order. -/
theorem crossings (C : Finset (Word 4)) (k l : Fin 4) (m m' : Fin 3)
    (hkl : k.succAbove m = l) (hlk : l.succAbove m' = k) (i j : ZMod 7) :
    let W := projectedBand C k i
    let W' := projectedBand C l j
    let proj := fun x : Word 4 => dropCoord m (dropCoord k x)
    cut W m j = cut W' m' i ∧
      cut W m j = (band C k i ∩ band C l j).image proj ∧
      ∀ s ∈ ({j, j+1} : Finset (ZMod 7)), lev W m s = (band C k i ∩ level C l s).image proj :=
  Proof.Crossings.crossings C k l m m' hkl hlk i j

/-- Lemma 9. Splitting the two bands at their common level reconstructs all three levels. -/
theorem slabs (C : Finset (Word 4)) (hC : IsCode C) (k : Fin 4) (c : ZMod 7) :
    let S := projectedBand C k (c-1)
    let T := projectedBand C k c
    let U := projectedLevel C k c
    let liftAt := fun (t : ZMod 7) (P : Finset (Word 3)) =>
      P.image (fun y : Word 3 => k.insertNth (α := fun _ => ZMod 7) t y)
    U ⊆ S ∩ T ∧ level C k (c-1) = liftAt (c-1) (S \ U) ∧
      level C k c = liftAt c U ∧ level C k (c+1) = liftAt (c+1) (T \ U) :=
  Proof.Crossings.slabs C hC k c

/-- Lemma 9, transverse part. W witnesses membership of the displayed triple in 𝒯₁. -/
theorem slabs_transverse (C : Finset (Word 4)) (hC : IsCode C)
    (k l : Fin 4) (m m' : Fin 3) (hkl : k.succAbove m = l) (hlk : l.succAbove m' = k)
    (c t : ZMod 7) (hfull : t ∈ fullStarts C l) :
    let W := projectedBand C l t
    let X := cut (projectedBand C k (c-1)) m t
    let Y := cut (projectedBand C k c) m t
    let M := cut (projectedLevel C k c) m t
    (IsCode W ∧ W.card = 33) ∧ (X, Y, M) = adjacentSignature W m' (c-1) ∧
      lev W m' (c-1) = X \ M ∧ lev W m' c = M ∧ lev W m' (c+1) = Y \ M :=
  Proof.Crossings.slabs_transverse C hC k l m m' hkl hlk c t hfull

theorem perfect_matching (S T : Finset (Word 3)) (hS : IsCode S) (hT : IsCode T)
    (s33 : S.card = 33) (t33 : T.card = 33) :
    ∃ e : ↥S ≃ ↥T, ∀ x : ↥S, conflictEdge x.val (e x).val :=
  Proof.Matching.perfect_matching card_le_thirty_three S T hS hT s33 t33

/-- Lemma 10. The count holds for any perfect matching selected by the search. -/
theorem matching_count (S T X Y : Finset (Word 3)) (hX : X ⊆ S) (hY : Y ⊆ T)
    (hdisj : Disjoint X Y) (hXY : IsCode (X ∪ Y)) (s33 : S.card = 33)
    (e : ↥S ≃ ↥T) (he : ∀ x : ↥S, conflictEdge x.val (e x).val) :
    (∀ x ∈ X, ∀ y ∈ Y, ¬conflictEdge x y) ∧
      (S.attach.filter fun x => x.val ∉ X ∧ (e x).val ∉ Y).card = 33 - X.card - Y.card :=
  Proof.Matching.matching_count S T X Y hX hY hdisj hXY s33 e he

/-- Lemma 11. A translation in the chosen axis and a single isometry on the
remaining axes send the first projected band to a literal atlas representative. -/
theorem normalise_full_pair (C : Finset (Word 4)) (hC : IsCode C) (k : Fin 4)
    (i d : ZMod 7) (hi : i ∈ fullStarts C k) (hid : i+d ∈ fullStarts C k) :
    ∃ γ : Isometry 4, ∃ g : Isometry 3,
      (∀ x : Word 4, act γ x 0 = x k - i ∧ dropCoord 0 (act γ x) = act g (dropCoord k x)) ∧
      IsCode (actOnCode γ C) ∧
      (∀ p, HasProfile C p ↔ HasProfile (actOnCode γ C) p) ∧
      0 ∈ fullStarts (actOnCode γ C) 0 ∧ d ∈ fullStarts (actOnCode γ C) 0 ∧
      ∃ r : Fin atlasPlanes.size, projectedBand (actOnCode γ C) 0 0 = atlasRepresentative r :=
  Proof.Crossings.normalise_full_pair atlas_complete C hC k i d hi hid

namespace SearchSpec

section Adjacent

variable {C : Points} {m : Frame} {k : Axis}
variable (hC : IsCode C) (hm : Marked m C) (hk : m.gap k = 1)
local notation "P" => projections m C
local notation "U" => plane C k (start m k true)
local notation "D" => C.filter (inUnion m)

include hC hm hk in
theorem adj_stage1_retains : AdjSupport k (P k false) (P k true) :=
  SevenCycle.Adjacent.support hC hm hk

include hC hm hk in
theorem adj_stage2_retains : Contacts m k (P k false) (P k true) :=
  Proof.FrameGeometry.contacts hC hm k

include hC hm hk in
theorem adj_stage3_retains : AdjMiddle m k (P k false) (P k true) U :=
  SevenCycle.Adjacent.middle hC hm hk

include hC hm hk in
theorem adj_stage4_retains : AdjSixBand m k (P k false) (P k true) U P :=
  SevenCycle.Adjacent.six_bands hC hm hk

include hC hm in
theorem adj_stage5_retains : AdjUnion m D :=
  SevenCycle.Adjacent.slab_union hC hm

include hC hm in
theorem adj_stage6_retains_1111 : Exterior m D (C \ D) :=
  SevenCycle.Adjacent.exterior hC m

include hC hm in
theorem adj_stage6_retains_mixed : Remaining m D P :=
  SevenCycle.Adjacent.remaining hC hm

end Adjacent

/-- Lemma 13 in the physical frame of a code with four adjacent full pairs. -/
theorem exterior_card_le_112 {C : Points} (hC : IsCode C) {m : Frame} (hm : Marked m C)
    (all : ∀ k, m.gap k = 1) : C.card ≤ 112 :=
  SevenCycle.Adjacent.FrontSearch.bound1111_of_run atlas_complete
    SevenCycle.Adjacent.PrefixHint.needed SevenCycle.Adjacent.FrontSearch.checked C hC m hm all

/-- Lemma 14 excludes the nine mixed profiles from the true marked slabs at
each of the code's adjacent axes. -/
theorem mixed_no_remaining {C : Points} (hC : IsCode C) {m : Frame} (hm : Marked m C)
    (adj : ∃ k, m.gap k = 1) (mixed : ∃ k, m.gap k ≠ 1) : False :=
  SevenCycle.Adjacent.MixedCommon.reject hC hm adj mixed fun k hk =>
    SevenCycle.Adjacent.FrontSearch.anchor_of_run atlas_complete
      SevenCycle.Adjacent.PrefixHint.needed SevenCycle.Adjacent.FrontSearch.checked C hC m hm k hk

/-- Proposition 12. -/
theorem exclude_adjacent (C : Points) (hC : IsCode C) (hc : C.card = 113)
    (p : Multiset ℕ) (hp : HasProfile C p) : 1 ∉ p := by
  intro h1
  obtain ⟨m, hm, _, rfl⟩ := Proof.Profiles.marked_frame card_le_thirty_three hC hc hp
  obtain ⟨k, _, hk⟩ := Multiset.mem_map.mp h1
  by_cases all : ∀ j, m.gap j = 1
  · have bound := exterior_card_le_112 hC hm all
    omega
  · exact mixed_no_remaining hC hm ⟨k,hk⟩ (Classical.not_forall.mp all)

section GapTwo

variable {C : Points} {m : Frame} {k : Axis}
variable (hC : IsCode C) (hm : Marked m C) (hk : m.gap k = 2)
local notation "P" => projections m C
local notation "X" => plane C k (m.base k + 1)
local notation "Y" => plane C k (start m k true)

include hC hm hk in
theorem two_stage1_retains : Contacts m k (P k false) (P k true) :=
  Proof.FrameGeometry.contacts hC hm k

include hC hm hk in
theorem two_stage2_retains (hc : C.card = 113) (hn : NoConsecutive C)
    (M : Finset (Word 4 × Word 4)) (hM : Perfect (P k false) (P k true) M) :
    TwoMiddle m k (P k false) (P k true) X Y M :=
  TypeTwo.middle_retains_113 card_le_thirty_three hC hm hk hc hn M hM

include hC hm hk in
theorem two_stage3_retains : TwoProjections m k (P k false) (P k true) X Y P :=
  TypeTwo.projections_retain hC hm hk

end GapTwo

/-- Lemma 16 on the normalized atlas coordinates. Each target interval
checks all first supports and all eight transverse gap assignments. -/
theorem two_no_join (i : Fin 64) : TypeTwo.Search.chunk i.val = true :=
  TypeTwo.Search.all_chunks i

/-- Proposition 15, equivalently the four profiles with minimum entry 2. -/
theorem exclude_two (C : Points) (hC : IsCode C) (hc : C.card = 113)
    (p : Multiset ℕ) (hp : HasProfile C p) (h1 : 1 ∉ p) : 2 ∉ p :=
  TypeTwo.Search.exclude_two_of_chunks card_le_thirty_three atlas_complete two_no_join C hC hc p hp h1

section GapThree

variable {C : Points} {m : Frame} {k : Axis}
variable (hC : IsCode C) (hm : Marked m C) (hg : ∀ i, m.gap i = 3)
local notation "P" => projections m C

include hC hm hg in
theorem three_pairs_retains : Contacts m k (P k false) (P k true) :=
  Proof.FrameGeometry.contacts hC hm k

include hC hm hg in
theorem three_join_retains : joined m k (P k false) (P k true) P :=
  Proof.FrameGeometry.projected_join hC hm k

end GapThree

/-- Lemma 18 on normalized atlas coordinates. Every translated anchor
representative is compared with every labelled opposite and transverse band. -/
theorem three_no_join : TypeThree.NoJoined (TypeThree.packRows atlasPlanes Bitsets.translationImages)
    (TypeThree.packRows atlasPlanes Bitsets.orbitImages) :=
  TypeThree.no_join

/-- Proposition 17 applies to codes of any size, even if an axis also has
a pair of full starts at a smaller distance. -/
theorem exclude_three (C : Points) (hC : IsCode C) :
    ¬ ∀ k, ∃ t, t ∈ fullStarts C k ∧ t + 3 ∈ fullStarts C k :=
  TypeThree.exclude C hC

end SearchSpec

/-- Section 8. A hypothetical larger code contains a 113-element subcode. -/
theorem reduce_to_113 (h : ∀ D : Finset (Word 4), IsCode D → D.card ≠ 113)
    (C : Finset (Word 4)) (hc : IsCode C) : C.card ≤ 112 := by
    by_contra! hlo
    obtain ⟨D, hsub, hcard⟩ := Finset.exists_subset_card_eq (show 113 ≤ C.card by omega)
    exact h D (fun x hx y hy => hc x (hsub hx) y (hsub hy)) hcard

private theorem orient_three : ∀ i j : ZMod 7, cycleDistance i j = 3 → i + 3 = j ∨ j + 3 = i := by
  unfold cycleDistance
  decide

theorem no_code_113 (C : Finset (Word 4)) (hc : IsCode C) : C.card ≠ 113 := by
    intro h113
    obtain ⟨p, hp⟩ := profile_exists card_le_thirty_three C hc h113
    have h1 := SearchSpec.exclude_adjacent C hc h113 p hp
    have h2 := SearchSpec.exclude_two C hc h113 p hp h1
    obtain ⟨d, hd, rfl⟩ := hp
    apply SearchSpec.exclude_three C hc
    intro k
    have hg : (d k).val + 1 = 3 := by
      have hn1 : (d k).val + 1 ≠ 1 := fun he => h1 (Multiset.mem_map.mpr ⟨k, Finset.mem_univ k, he⟩)
      have hn2 : (d k).val + 1 ≠ 2 := fun he => h2 (Multiset.mem_map.mpr ⟨k, Finset.mem_univ k, he⟩)
      have := (d k).isLt
      omega
    obtain ⟨i, hi, j, hj, _, hdist⟩ := (hd k).1
    rcases orient_three i j (hdist.trans hg) with he | he
    · exact ⟨i, hi, he.symm ▸ hj⟩
    · exact ⟨j, hj, he.symm ▸ hi⟩

end SevenCycle.Blueprint

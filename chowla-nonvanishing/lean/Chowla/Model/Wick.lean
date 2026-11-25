import Chowla.Model.Centred

namespace Chowla

open MeasureTheory MvPolynomial
open scoped BigOperators

variable {ι : Type*} [LinearOrder ι]

/-- A Wick block is either an unmatched position or a permitted internal pair. -/
noncomputable def wickBlock (h : ι → FourierProfile) (pairs : Finset (Finset ι)) (T : Finset ι) :
    Model :=
  if T.card = 1 then ∏ i ∈ T, centered (h i)
  else if T.card = 2 ∧ T ∈ pairs then C (-blockCumulant h T)
  else 0

/-- Wick ordering with a specified set of allowed internal pairs. -/
noncomputable def selectiveWick (h : ι → FourierProfile) (pairs : Finset (Finset ι))
    (S : Finset ι) : Model :=
  partitionWeight (wickBlock h pairs) S

theorem partitionWeight_congr {R} [CommSemiring R] (w v : Finset ι → R) (S : Finset ι)
    (he : ∀ B ⊆ S, B ≠ ∅ → w B = v B) : partitionWeight w S = partitionWeight v S := by
  unfold partitionWeight
  apply Finset.sum_congr rfl
  intro P _
  apply Finset.prod_congr rfl
  intro B hB
  exact he B (P.le hB) (P.ne_bot hB)

theorem selectiveWick_empty (h : ι → FourierProfile) (S : Finset ι) :
    selectiveWick h ∅ S = ∏ i ∈ S, centered (h i) := by
  classical
  have hweight : wickBlock h ∅ = fun T =>
      @ite Model (T.card = 1) (Classical.propDecidable _) (∏ i ∈ T, centered (h i)) 0 := by
    funext T
    by_cases hT : T.card = 1 <;> simp [wickBlock, hT]
  rw [selectiveWick, hweight]
  have hfilter := partitionWeight_filter (fun T : Finset ι => ∏ i ∈ T, centered (h i)) S
    (fun T => T.card = 1)
  rw [hfilter]
  have hs : (Finset.univ.filter fun P : Finpartition S => ∀ T ∈ P.parts, T.card = 1) = {⊥} := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hp
      apply Finpartition.ext
      ext T
      rw [Finpartition.mem_bot_iff]
      constructor
      · intro hT
        obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (hp T hT)
        exact ⟨i, P.le hT (Finset.mem_singleton_self _), rfl⟩
      · rintro ⟨i, hi, rfl⟩
        obtain ⟨A, hA, _⟩ := P.existsUnique_mem hi
        obtain ⟨j, hAj⟩ := Finset.card_eq_one.mp (hp A hA.1)
        have hij : i = j := Finset.mem_singleton.mp (hAj ▸ hA.2)
        rw [hij, ← hAj]
        exact hA.1
    · rintro rfl T hT
      obtain ⟨i, _, rfl⟩ := Finpartition.mem_bot_iff.mp hT
      simp
  calc
    _ = ∑ P ∈ ({⊥} : Finset (Finpartition S)), ∏ T ∈ P.parts, ∏ i ∈ T, centered (h i) := by
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext P
      rw [← hs]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    _ = _ := by
      rw [Finset.sum_singleton, Finpartition.parts_bot, Finset.prod_map]
      simp

/-- Adding one permitted pair adds its negative covariance times the polynomial of the
remaining positions. -/
theorem selectiveWick_insert_pair (h : ι → FourierProfile) (pairs : Finset (Finset ι))
    {B S : Finset ι} (hcard : B.card = 2) (hBp : B ∉ pairs) (hBS : B ⊆ S) :
    selectiveWick h (insert B pairs) S = selectiveWick h pairs S +
      C (-blockCumulant h B) * selectiveWick h pairs (S \ B) := by
  classical
  have hBne : B ≠ ∅ := by
    rintro rfl
    simp at hcard
  have hw : wickBlock h (insert B pairs) = fun T =>
      if T = B then wickBlock h pairs T + C (-blockCumulant h B) else wickBlock h pairs T := by
    funext T
    by_cases hT : T = B
    · subst T
      simp [wickBlock, hcard, hBp]
    · simp [wickBlock, hT]
  rw [selectiveWick, hw, partitionWeight_update _ _ hBS hBne]
  rfl

theorem selectiveWick_insert_pair_of_not_subset (h : ι → FourierProfile) (pairs : Finset (Finset ι))
    {B S : Finset ι} (hBS : ¬ B ⊆ S) :
    selectiveWick h (insert B pairs) S = selectiveWick h pairs S := by
  apply partitionWeight_congr
  intro T hTS _
  have hne : T ≠ B := fun he => hBS (he ▸ hTS)
  simp [wickBlock, hne]

theorem wick_eq_selectiveWick (hs : List FourierProfile) :
    wick hs = selectiveWick hs.get
      ((Finset.univ : Finset (Fin hs.length)).powerset.filter fun T => T.card = 2)
      Finset.univ := by
  classical
  let U : Finset (Fin hs.length) := Finset.univ
  let F := U.powerset.filter fun T => T.card = 2
  let w : Finset (Fin hs.length) → Model := fun T =>
    match (T.sort (· ≤ ·)).map hs.get with
    | [h] => centered h
    | [h, g] => C (-cumulant [h, g])
    | _ => 1
  change (∑ P ∈ (Finset.univ.filter fun P : Finpartition U => ∀ T ∈ P.parts, T.card ≤ 2),
      ∏ T ∈ P.parts, w T) = partitionWeight (wickBlock hs.get F) U
  let keep : Finset (Fin hs.length) → Prop := fun T => T.card ≤ 2
  have hf := partitionWeight_filter w U keep
  refine (Finset.sum_congr ?_ (fun _ _ => rfl)).trans (hf.symm.trans ?_)
  · ext P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, keep]
  apply partitionWeight_congr
  intro T hTS hTne
  have hTcardpos : 0 < T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hTne)
  by_cases hcard1 : T.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard1
    simp [keep, w, wickBlock]
  · by_cases hcard2 : T.card = 2
    · have hTlist : ((T.sort (· ≤ ·)).map hs.get).length = 2 := by simpa using hcard2
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hTlist
      simp [keep, hcard2, w, hab, wickBlock, blockCumulant, F, hTS]
    · have hlarge : ¬ T.card ≤ 2 := by omega
      simp [keep, hlarge, wickBlock, hcard1, hcard2]

noncomputable def allPairs (S : Finset ι) : Finset (Finset ι) :=
  S.powerset.filter fun T => T.card = 2

theorem selectiveWick_embedding {κ : Type*} [LinearOrder κ]
    (h : ι → FourierProfile) (g : κ → FourierProfile) (e : ι ↪ κ)
    (S : Finset ι) (pairs : Finset (Finset ι))
    (hg : ∀ i ∈ S, g (e i) = h i) (hh : ∀ i ∈ S, IsProfile (h i)) :
    selectiveWick h pairs S = selectiveWick g
      (pairs.map (Finset.mapEmbedding e).toEmbedding) (S.map e) := by
  classical
  unfold selectiveWick partitionWeight
  refine Finset.sum_equiv (finpartitionEmbedding e S) (fun _ => by simp) ?_
  intro P _
  rw [finpartitionEmbedding_parts, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro T hT
  have hTe : T.map e ∈ pairs.map (Finset.mapEmbedding e).toEmbedding ↔ T ∈ pairs :=
    Finset.mem_map' (Finset.mapEmbedding e).toEmbedding
  change wickBlock h pairs T = wickBlock g _ (T.map e)
  simp only [wickBlock, Finset.card_map, hTe]
  split_ifs with hs hp
  · rw [Finset.prod_map]
    exact Finset.prod_congr rfl fun i hi => congrArg centered (hg i (P.le hT hi)).symm
  · exact congrArg (fun x => C (-x)) (blockCumulant_map h g e T
      (fun i hi => hg i (P.le hT hi)) (fun i hi => hh i (P.le hT hi)))
  · rfl

omit [LinearOrder ι] in
theorem allPairs_map {κ : Type*} (e : ι ↪ κ) (S : Finset ι) :
    (allPairs S).map (Finset.mapEmbedding e).toEmbedding = allPairs (S.map e) := by
  classical
  ext T
  constructor
  · intro hT
    obtain ⟨B, hB, rfl⟩ := Finset.mem_map.mp hT
    have hm := Finset.mem_filter.mp hB
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Finset.map_subset_map.mpr (Finset.mem_powerset.mp hm.1)),
      by change (B.map e).card = 2; rw [Finset.card_map]; exact hm.2⟩
  · intro hT
    have hm : T ⊆ S.map e ∧ T.card = 2 := by
      simpa [allPairs] using hT
    obtain ⟨B, hB, rfl⟩ := Finset.subset_map_iff.mp hm.1
    exact Finset.mem_map.mpr ⟨B, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hB,
      by simpa only [Finset.card_map] using hm.2⟩, rfl⟩

end Chowla

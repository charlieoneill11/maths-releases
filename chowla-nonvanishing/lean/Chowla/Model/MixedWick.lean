import Chowla.Model.Wick

namespace Chowla

open MeasureTheory MvPolynomial
open scoped BigOperators

variable {ι : Type*} [LinearOrder ι]

noncomputable def mixedWick (h : ι → FourierProfile) (U A B : Finset ι)
    (F G : Finset (Finset ι)) : Model :=
  (∏ i ∈ U \ (A ∪ B), stat (h i)) * selectiveWick h F A * selectiveWick h G B

noncomputable def mixedCumulant (h : ι → FourierProfile) (A B : Finset ι)
    (F G : Finset (Finset ι)) (T : Finset ι) : ℝ := by
  classical
  exact if T.card = 2 ∧ ((T ∈ F ∧ T ⊆ A) ∨ (T ∈ G ∧ T ⊆ B)) then 0
    else selectiveCumulant h (A ∪ B) T

theorem modelExpectation_add (P Q : Model) :
    modelExpectation (P + Q) = modelExpectation P + modelExpectation Q := by
  simp only [modelExpectation_eq_linear, map_add]

private theorem mixedWick_comm (h : ι → FourierProfile) (U A B : Finset ι)
    (F G : Finset (Finset ι)) :
    mixedWick h U A B F G = mixedWick h U B A G F := by
  rw [mixedWick, mixedWick, Finset.union_comm A B]
  ring

private theorem mixedCumulant_comm (h : ι → FourierProfile) (A B : Finset ι)
    (F G : Finset (Finset ι)) :
    mixedCumulant h A B F G = mixedCumulant h B A G F := by
  funext T
  simp only [mixedCumulant]
  simp only [or_comm, Finset.union_comm]

private theorem mixedWick_empty (h : ι → FourierProfile) {U A B : Finset ι}
    (hA : A ⊆ U) (hB : B ⊆ U) (hAB : Disjoint A B) (hh : ∀ i ∈ U, IsProfile (h i)) :
    modelExpectation (mixedWick h U A B ∅ ∅) =
      partitionWeight (mixedCumulant h A B ∅ ∅) U := by
  classical
  have hsub : A ∪ B ⊆ U := Finset.union_subset hA hB
  have hpoly : mixedWick h U A B ∅ ∅ = ∏ i ∈ U, selectiveStat h (A ∪ B) i := by
    rw [mixedWick, selectiveWick_empty, selectiveWick_empty]
    rw [mul_assoc, ← Finset.prod_union hAB, ← Finset.prod_sdiff hsub]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      exact (if_neg (Finset.mem_sdiff.mp hi).2).symm
    · apply Finset.prod_congr rfl
      intro i hi
      exact (if_pos hi).symm
  rw [hpoly, selective_moment h _ U hsub hh]
  congr 1
  funext T
  simp [mixedCumulant]

private theorem mixedCumulant_sdiff_left (h : ι → FourierProfile) (A B S : Finset ι)
    (F G : Finset (Finset ι)) {T : Finset ι} (hTS : Disjoint T S) :
    mixedCumulant h A B F G T = mixedCumulant h (A \ S) B F G T := by
  classical
  have hsub : T ⊆ A \ S ↔ T ⊆ A := by
    constructor
    · exact fun hT x hx => (Finset.mem_sdiff.mp (hT hx)).1
    · exact fun hT x hx => Finset.mem_sdiff.mpr ⟨hT hx, fun hS => Finset.disjoint_left.mp hTS hx hS⟩
  have hsel : selectiveCumulant h (A ∪ B) T =
      selectiveCumulant h ((A \ S) ∪ B) T := by
    have he : (∃ i ∈ A ∪ B, T = {i}) ↔ ∃ i ∈ (A \ S) ∪ B, T = {i} := by
      constructor
      · rintro ⟨i, hi, hT⟩
        have hni : i ∉ S := fun hm =>
          Finset.disjoint_left.mp hTS (hT ▸ Finset.mem_singleton_self i) hm
        refine ⟨i, ?_, hT⟩
        rcases Finset.mem_union.mp hi with ha | hb
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha, hni⟩)
        · exact Finset.mem_union_right _ hb
      · rintro ⟨i, hi, hT⟩
        refine ⟨i, ?_, hT⟩
        rcases Finset.mem_union.mp hi with ha | hb
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp ha).1
        · exact Finset.mem_union_right _ hb
    simp only [selectiveCumulant, he]
  simp only [mixedCumulant, hsub, hsel]

private theorem mixedWick_insert_left
    (h : ι → FourierProfile) {U A B S : Finset ι} (F G : Finset (Finset ι))
    (hA : A ⊆ U) (hAB : Disjoint A B) (hc : S.card = 2) (hF : S ∉ F)
    (hcur : modelExpectation (mixedWick h U A B F G) =
      partitionWeight (mixedCumulant h A B F G) U)
    (hrem : modelExpectation (mixedWick h (U \ S) (A \ S) B F G) =
      partitionWeight (mixedCumulant h (A \ S) B F G) (U \ S)) :
    modelExpectation (mixedWick h U A B (insert S F) G) =
      partitionWeight (mixedCumulant h A B (insert S F) G) U := by
  classical
  by_cases hs : S ⊆ A
  · have hne : S ≠ ∅ := by rintro rfl; simp at hc
    have hsB : ¬ S ⊆ B := by
      intro hSB
      exact hne (disjoint_self.mp (hAB.mono hs hSB))
    let K := blockCumulant h S
    have hrest : (U \ S) \ ((A \ S) ∪ B) = U \ (A ∪ B) := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_union]
      have himp : i ∈ S → i ∈ A := fun hi => hs hi
      tauto
    have hpoly :
        mixedWick h U A B (insert S F) G =
          mixedWick h U A B F G + C (-K) * mixedWick h (U \ S) (A \ S) B F G := by
      simp only [mixedWick, selectiveWick_insert_pair h F hc hF hs, hrest]
      ring
    have hweight : mixedCumulant h A B (insert S F) G = fun T =>
        if T = S then mixedCumulant h A B F G T + (-K) else mixedCumulant h A B F G T := by
      funext T
      by_cases hT : T = S
      · subst T
        have hs' : ¬ ∃ i, (i ∈ A ∨ i ∈ B) ∧ S = {i} := by
          rintro ⟨i, _, he⟩
          simp [he] at hc
        simp [mixedCumulant, selectiveCumulant, hc, hs, hF, hsB, hs', K]
      · simp [mixedCumulant, hT]
    have hweight_rem : partitionWeight (mixedCumulant h A B F G) (U \ S) =
        partitionWeight (mixedCumulant h (A \ S) B F G) (U \ S) := by
      apply partitionWeight_congr
      intro T hT _
      exact mixedCumulant_sdiff_left h A B S F G (disjoint_sdiff_self_left.mono_left hT)
    rw [hpoly, modelExpectation_add, modelExpectation_C_mul, hcur, hrem, hweight,
      partitionWeight_update _ (-K) (hs.trans hA) hne, hweight_rem]
  · have hweight : mixedCumulant h A B (insert S F) G = mixedCumulant h A B F G := by
      funext T
      by_cases hT : T = S
      · subst T
        simp [mixedCumulant, hs]
      · simp [mixedCumulant, hT]
    rwa [hweight, mixedWick, selectiveWick_insert_pair_of_not_subset h F hs]

/-- The marked Wick expectation is the partition sum with all chosen internal pairs and
centered singletons deleted. -/
theorem mixed_wick_moment (h : ι → FourierProfile) (U A B : Finset ι)
    (F G : Finset (Finset ι)) (hA : A ⊆ U) (hB : B ⊆ U) (hAB : Disjoint A B)
    (hh : ∀ i ∈ U, IsProfile (h i))
    (hF : ∀ T ∈ F, T.card = 2) (hG : ∀ T ∈ G, T.card = 2) :
    modelExpectation (mixedWick h U A B F G) =
      partitionWeight (mixedCumulant h A B F G) U := by
  classical
  let n := F.card + G.card
  have hn : n = F.card + G.card := rfl
  clear_value n
  induction n using Nat.strong_induction_on generalizing U A B F G with
  | h n ih =>
    have step (U A B : Finset ι) (F G : Finset (Finset ι)) (hA : A ⊆ U) (hB : B ⊆ U)
        (hAB : Disjoint A B) (hh : ∀ i ∈ U, IsProfile (h i))
        (hF : ∀ T ∈ F, T.card = 2) (hG : ∀ T ∈ G, T.card = 2)
        (hn : n = F.card + G.card) (hFne : F.Nonempty) :
        modelExpectation (mixedWick h U A B F G) =
          partitionWeight (mixedCumulant h A B F G) U := by
      obtain ⟨S, hS⟩ := hFne
      let E := F.erase S
      have hE : ∀ T ∈ E, T.card = 2 := fun T hT => hF T (Finset.mem_erase.mp hT).2
      have hEc : E.card + G.card < n := by
        rw [hn, Finset.card_erase_of_mem hS]
        have hpos := Finset.card_pos.mpr (show F.Nonempty from ⟨S, hS⟩)
        omega
      by_cases hSA : S ⊆ A
      · have hB' : B ⊆ U \ S := by
          intro x hx
          exact Finset.mem_sdiff.mpr ⟨hB hx, fun hsx => Finset.disjoint_left.mp hAB (hSA hsx) hx⟩
        have hA' : A \ S ⊆ U \ S := fun _ hx =>
          Finset.mem_sdiff.mpr ⟨hA (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
        have hAB' : Disjoint (A \ S) B := hAB.mono_left Finset.sdiff_subset
        have hcur := ih _ hEc U A B E G hA hB hAB hh hE hG rfl
        have hrem := ih _ hEc (U \ S) (A \ S) B E G hA' hB' hAB'
          (fun i hi => hh i (Finset.mem_sdiff.mp hi).1) hE hG rfl
        have hresult := mixedWick_insert_left h E G hA hAB (hF S hS)
          (Finset.notMem_erase _ _) hcur hrem
        rwa [Finset.insert_erase hS] at hresult
      · have hcur := ih _ hEc U A B E G hA hB hAB hh hE hG rfl
        have hEq : mixedWick h U A B F G = mixedWick h U A B E G := by
          rw [← Finset.insert_erase hS, mixedWick, mixedWick,
            selectiveWick_insert_pair_of_not_subset h E hSA]
        have hweight : mixedCumulant h A B F G = mixedCumulant h A B E G := by
          funext T
          by_cases he : T = S
          · subst T
            simp [mixedCumulant, hSA]
          · simp [mixedCumulant, E, he]
        rwa [hEq, hweight]
    rcases F.eq_empty_or_nonempty with h0 | he
    · rcases G.eq_empty_or_nonempty with h1 | heG
      · subst F G
        exact mixedWick_empty h hA hB hAB hh
      · rw [mixedWick_comm h U A B F G, mixedCumulant_comm h A B F G]
        exact step U B A G F hB hA hAB.symm hh hG hF (hn.trans (Nat.add_comm ..)) heG
    · exact step U A B F G hA hB hAB hh hF hG hn he

end Chowla

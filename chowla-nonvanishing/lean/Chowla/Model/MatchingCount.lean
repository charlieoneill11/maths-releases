import Chowla.CheckerPartitionBridge
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Basic

namespace Chowla

open scoped BigOperators
open Polynomial

private theorem crossPair_count_step (a b j : ℕ) :
    (a + 1).choose (j + 1) * b.choose (j + 1) * (j + 1).factorial =
      a.choose (j + 1) * b.choose (j + 1) * (j + 1).factorial +
      b * (a.choose j * (b - 1).choose j * j.factorial) := by
  cases b with
  | zero => simp
  | succ b =>
    have hb : (b + 1) * b.choose j = (b + 1).choose (j + 1) * (j + 1) :=
      Nat.add_one_mul_choose_eq b j
    simp only [Nat.add_sub_cancel, Nat.choose_succ_succ' a j,
      Nat.factorial_succ]
    calc
      _ = a.choose (j + 1) * (b + 1).choose (j + 1) * ((j + 1) * j.factorial) +
          (b + 1).choose (j + 1) * (j + 1) * (a.choose j * j.factorial) := by ring
      _ = _ := by rw [← hb]; ring

private theorem crossPair_polynomial_coeff {ι : Type*} [DecidableEq ι]
    (L : Finset ι) (p : Finset ι → Polynomial ℕ)
    (hbase : ∀ U, U ∩ L = ∅ → p U = 1)
    (hstep : ∀ U i, i ∈ U → i ∈ L → p U = p (U.erase i) +
      ∑ k ∈ U \ L, X * p (U \ {i, k}))
    (U : Finset ι) (j : ℕ) :
    (p U).coeff j = (U ∩ L).card.choose j * (U \ L).card.choose j * j.factorial := by
  induction U using Finset.strongInduction generalizing j with
  | H U ih =>
    by_cases hleft : U ∩ L = ∅
    · rw [hbase U hleft, hleft]
      cases j <;> simp [Polynomial.coeff_one]
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hleft
      have hiU := (Finset.mem_inter.mp hi).1
      have hL := (Finset.mem_inter.mp hi).2
      have hLeftErase : U.erase i ∩ L = (U ∩ L).erase i := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_inter]
        tauto
      have hRightErase : U.erase i \ L = U \ L := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        have hx : x = i → x ∈ L := fun he => he ▸ hL
        tauto
      have hLeftPair (k : ι) (hk : k ∈ U \ L) : (U \ {i, k}) ∩ L = (U ∩ L).erase i := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_inter, Finset.mem_insert,
          Finset.mem_singleton]
        have hx : x = k → x ∉ L := fun he => he ▸ (Finset.mem_sdiff.mp hk).2
        tauto
      have hRightPair (k : ι) (hk : k ∈ U \ L) : (U \ {i, k}) \ L = (U \ L).erase k := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        have hx : x = i → x ∈ L := fun he => he ▸ hL
        tauto
      have hErase : U.erase i ⊂ U := Finset.erase_ssubset hiU
      have hPair (k : ι) : U \ {i, k} ⊂ U := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
        intro he
        have hU : i ∈ U \ {i, k} := he.symm ▸ hiU
        simp at hU
      rw [hstep U i hiU hL, Polynomial.coeff_add, Polynomial.finset_sum_coeff, ih _ hErase,
        hLeftErase, hRightErase, Finset.card_erase_of_mem hi]
      cases j with
      | zero => simp
      | succ j =>
        simp only [Polynomial.coeff_X_mul]
        have hsum :
            (∑ k ∈ U \ L, (p (U \ {i, k})).coeff j) =
            (U \ L).card * (((U ∩ L).card - 1).choose j *
              ((U \ L).card - 1).choose j * j.factorial) := by
          calc
            _ = ∑ k ∈ U \ L, (((U ∩ L).card - 1).choose j *
                  ((U \ L).card - 1).choose j * j.factorial) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [ih _ (hPair k), hLeftPair k hk, hRightPair k hk,
                Finset.card_erase_of_mem hi, Finset.card_erase_of_mem hk]
            _ = _ := by simp
        rw [hsum]
        have hcard : (U ∩ L).card - 1 + 1 = (U ∩ L).card :=
          Nat.sub_add_cancel (Finset.card_pos.mpr ⟨i, hi⟩)
        simpa only [hcard] using
          (crossPair_count_step ((U ∩ L).card - 1) ((U \ L).card) j).symm

private theorem crossPair_monomial {ι : Type*} [DecidableEq ι] (L B : Finset ι) :
    Checker.crossBlockWeight L (fun _ _ => (X : Polynomial ℕ)) B =
      if B.card = 1 then 1 else
        if B.card = 2 ∧ (∃ i ∈ B, i ∈ L) ∧ (∃ i ∈ B, i ∉ L) then X else 0 := by
  classical
  by_cases h₁ : B.card = 1
  · simp only [Checker.crossBlockWeight, if_pos h₁]
  · by_cases h₂ : B.card = 2
    · simp only [Checker.crossBlockWeight, if_neg h₁, if_pos h₂]
      by_cases hL : ∃ i ∈ B, i ∈ L
      · rcases hL with ⟨i, hi, hiL⟩
        by_cases hR : ∃ j ∈ B, j ∉ L
        · rcases hR with ⟨j, hj, hjL⟩
          have hij : i ≠ j := fun e => hjL (e ▸ hiL)
          have hB : B = {i, j} := by
            symm
            apply Finset.eq_of_subset_of_card_le
            · intro k hk
              rcases Finset.mem_insert.mp hk with rfl | hk
              · exact hi
              · exact (Finset.mem_singleton.mp hk).symm ▸ hj
            · rw [Finset.card_pair hij, h₂]
          rw [if_pos ⟨h₂, ⟨i, hi, hiL⟩, j, hj, hjL⟩, hB]
          simp [Finset.filter_insert, Finset.filter_singleton, hiL, hjL]
        · have he : B.filter (· ∉ L) = ∅ := by
            apply Finset.filter_eq_empty_iff.mpr
            intro j hj hjL
            exact hR ⟨j, hj, hjL⟩
          rw [if_neg (fun h => hR h.2.2), he]
          simp
      · have he : B.filter (· ∈ L) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro i hi hiL
          exact hL ⟨i, hi, hiL⟩
        rw [if_neg (fun h => hL h.2.1), he, Finset.sum_empty]
    · simp [Checker.crossBlockWeight, h₁, h₂]

private def crossPairAllowed {ι : Type*} [DecidableEq ι] (L : Finset ι) {U : Finset ι}
    (P : Finpartition U) : Prop :=
  ∀ B ∈ P.parts, B.card = 1 ∨ B.card = 2 ∧ (∃ i ∈ B, i ∈ L) ∧ (∃ i ∈ B, i ∉ L)

private theorem crossPair_count_coeff {ι : Type*} [DecidableEq ι] (L U : Finset ι) (j : ℕ) :
    (Checker.supportWeighted (Checker.crossBlockWeight L (fun _ _ => (X : Polynomial ℕ)))
        (fun _ => 1) U).coeff j =
      (by
        classical
        exact Fintype.card {P : Finpartition U // crossPairAllowed L P ∧ (pairParts P).card = j}) := by
  classical
  let g := Checker.crossBlockWeight L (fun _ _ => (X : Polynomial ℕ))
  have hf (P : Finpartition U) :
      ((∏ B ∈ P.parts, g B) * 1).coeff j =
        if crossPairAllowed L P ∧ (pairParts P).card = j then 1 else 0 := by
    rw [mul_one]
    by_cases hP : crossPairAllowed L P
    · have hprod : (∏ B ∈ P.parts, g B) = (X : Polynomial ℕ) ^ (pairParts P).card := by
        calc
          _ = ∏ B ∈ P.parts, if B.card = 2 then (X : Polynomial ℕ) else 1 := by
            apply Finset.prod_congr rfl
            intro B hB
            change Checker.crossBlockWeight L (fun _ _ => (X : Polynomial ℕ)) B = _
            rw [crossPair_monomial]
            rcases hP B hB with h | h
            · simp [h]
            · have hne : B.card ≠ 1 := by omega
              rw [if_neg hne, if_pos h, if_pos h.1]
          _ = ∏ B ∈ pairParts P, (X : Polynomial ℕ) := by
            rw [pairParts, Finset.prod_filter]
          _ = _ := Finset.prod_const _
      rw [hprod, Polynomial.coeff_X_pow]
      simp [hP, eq_comm]
    · have hb : ¬ ∀ B ∈ P.parts,
          B.card = 1 ∨ B.card = 2 ∧ (∃ i ∈ B, i ∈ L) ∧ (∃ i ∈ B, i ∉ L) := hP
      push Not at hb
      obtain ⟨B, hB, hc1, hc2⟩ := hb
      have hz : g B = 0 := by
        change Checker.crossBlockWeight L (fun _ _ => (X : Polynomial ℕ)) B = _
        have hbad : ¬(B.card = 2 ∧ (∃ i ∈ B, i ∈ L) ∧ (∃ i ∈ B, i ∉ L)) := by
          rintro ⟨h2, hL, i, hi, hiL⟩
          exact hiL (hc2 h2 hL i hi)
        rw [crossPair_monomial, if_neg hc1, if_neg hbad]
      rw [Finset.prod_eq_zero hB hz, Polynomial.coeff_zero]
      simp [hP]
  unfold Checker.supportWeighted
  rw [Polynomial.finset_sum_coeff]
  have he :
      (∑ P : Finpartition U, ((∏ B ∈ P.parts, g B) * 1).coeff j) =
      ∑ P : Finpartition U, if crossPairAllowed L P ∧ (pairParts P).card = j then 1 else 0 :=
    Finset.sum_congr rfl (fun P _ => hf P)
  change (∑ P : Finpartition U, ((∏ B ∈ P.parts, g B) * 1).coeff j) = _
  rw [he, ← Finset.sum_filter, Finset.sum_const]
  simp only [nsmul_eq_mul, mul_one]
  exact (Fintype.card_subtype _).symm

/-- The number of cross-row matchings with a fixed number of pairs. -/
theorem equal_width_matching_count (a b j : ℕ) :
    Fintype.card {P : Finpartition (Finset.univ : Finset (Fin (a + b))) //
      (∀ pair ∈ P.parts, pair.card = 1 ∨ (pair.card = 2 ∧
        (∃ i ∈ pair, i.val < a) ∧ (∃ i ∈ pair, a ≤ i.val))) ∧
      (P.parts.filter fun pair => pair.card = 2).card = j} =
      a.choose j * b.choose j * j.factorial := by
  classical
  let U : Finset (Fin (a + b)) := Finset.univ
  let L : Finset (Fin (a + b)) := Finset.univ.filter fun i => i.val < a
  let g := Checker.crossBlockWeight L (fun _ _ => (X : Polynomial ℕ))
  let p := fun S => Checker.supportWeighted g (fun _ => 1) S
  have hL : (U ∩ L).card = a := by
    change (Finset.univ ∩ L).card = a
    rw [Finset.univ_inter]
    exact Fin.card_filter_val_lt.trans (min_eq_right (Nat.le_add_right a b))
  have hR : (U \ L).card = b := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hLa : L.card = a := by simpa only [U, Finset.univ_inter] using hL
    simp [hLa]
  have hpbase (S : Finset (Fin (a + b))) (hS : S ∩ L = ∅) : p S = 1 :=
    Checker.supportWeighted_cross_right _ _ _ _ (Finset.disjoint_iff_inter_eq_empty.mpr hS)
  have hpstep (S : Finset (Fin (a + b))) (i : Fin (a + b)) (hiS : i ∈ S) (hiL : i ∈ L) :
      p S = p (S.erase i) + ∑ k ∈ S \ L, X * p (S \ {i, k}) :=
    Checker.supportWeighted_cross_left _ _ _ _ _ hiS hiL
  have hn := crossPair_polynomial_coeff L p hpbase hpstep U j
  rw [hL, hR] at hn
  refine Eq.trans ?_ hn
  refine Eq.trans ?_ (crossPair_count_coeff L U j).symm
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro P
  simp only [crossPairAllowed, pairParts, L, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]

end Chowla

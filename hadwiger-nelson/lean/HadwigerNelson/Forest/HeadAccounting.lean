import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Deterministic accounting for incoming edges at one head. Inner-tail events
are mutually exclusive. A maximum-credit tail bounds every charge involving
that tail, including intersections with the other events. -/

namespace HadwigerNelson.Forest
open scoped BigOperators

theorem head_max_sum {ι : Type*} (S : Finset ι) (h : ι → ℝ) (c M ε : ℝ)
    (hn : ∀ i ∈ S, 0 ≤ h i) (hc : 0 ≤ c) (hcM : c ≤ M) (he : 0 ≤ ε) :
    c + (∑ i ∈ S, max (h i-M) 0) - ε ≤ max c ((∑ i ∈ S, h i)-ε) := by
  by_cases small : ∀ i ∈ S, h i ≤ M
  · have sum0 : (∑ i ∈ S, max (h i-M) 0)=0 := Finset.sum_eq_zero (fun i hi =>
      max_eq_right (sub_nonpos.mpr (small i hi)))
    rw [sum0]
    exact (by linarith : c+0-ε≤c).trans (le_max_left ..)
  push_neg at small
  obtain ⟨j,hj,hgt⟩ := small
  have lower := Finset.single_le_sum (f:=fun i => min (h i) M) (fun i hi => le_min (hn i hi) (hc.trans hcM)) hj
  dsimp only at lower
  rw [min_eq_right hgt.le] at lower
  have split : (∑ i ∈ S, h i) = (∑ i ∈ S, min (h i) M) + ∑ i ∈ S, max (h i-M) 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases le_total (h i) M with hi | hi
    · rw [min_eq_left hi,max_eq_right (sub_nonpos.mpr hi),add_zero]
    · rw [min_eq_right hi,max_eq_left (sub_nonneg.mpr hi)]
      linarith
  exact (by linarith : c+ (∑ i ∈ S, max (h i-M) 0)-ε ≤ (∑ i ∈ S,h i)-ε).trans (le_max_right ..)

section
variable {ι : Type*} [DecidableEq ι]
private def pairCharge (B : Finset ι) (h : ι → ℝ) (i j : ι) : ℝ :=
  if i ≠ j ∧ ¬(i ∈ B ∧ j ∈ B) then min (h i) (h j) else 0

private theorem pairCharge_symm (B : Finset ι) (h : ι → ℝ) (i j : ι) :
    pairCharge B h i j = pairCharge B h j i := by
  have cond : (i≠j ∧ ¬(i∈B ∧ j∈B)) ↔ (j≠i ∧ ¬(j∈B ∧ i∈B)) := by grind
  simp only [pairCharge,cond,min_comm (h j) (h i)]

/-- Finite form of the Bonferroni estimate used in Lemma 38. The lower bound
on a union is sufficient if it pays each individual event and the sum of the
pairwise disjoint inner-tail events. -/
theorem charged_union (S B : Finset ι) (h : ι → ℝ) (Y : ℝ) (nonneg : ∀ i ∈ S, 0 ≤ h i)
    (paid : ∀ i ∈ S, h i ≤ Y) (inner : (∑ i ∈ S.filter (· ∈ B),h i) ≤ Y) :
    (∑ i ∈ S,h i) - (∑ u ∈ S, ∑ v ∈ S,
      if u ≠ v ∧ ¬(u ∈ B ∧ v ∈ B) then min (h u) (h v) else 0)/2 ≤ Y := by
  classical
  by_cases empty : S = ∅
  · simpa [empty] using inner
  obtain ⟨j,hj,big⟩ := Finset.exists_max_image S h (Finset.nonempty_iff_ne_empty.mpr empty)
  let P := pairCharge B h
  have pos {u v} (hu : u ∈ S) (hv : v ∈ S) : 0 ≤ P u v := by
    unfold P pairCharge
    split
    · exact le_min (nonneg u hu) (nonneg v hv)
    · exact le_rfl
  have rows : (∑ u ∈ S,∑ v ∈ S,P u v) =
      (∑ u ∈ S.erase j,∑ v ∈ S,P u v) + ∑ v ∈ S, P j v :=
    (Finset.sum_erase_add _ _ hj).symm
  have col : (∑ v ∈ S.erase j,P j v) ≤ ∑ u ∈ S.erase j, ∑ v ∈ S,P u v := by
    apply Finset.sum_le_sum
    intro u hu
    rw [show P j u=P u j from pairCharge_symm ..]
    exact Finset.single_le_sum (fun v hv => pos (Finset.mem_of_mem_erase hu) hv) hj
  have diag : P j j=0 := by simp [P,pairCharge]
  have pick := Finset.sum_erase_add S (P j) hj
  rw [diag,add_zero] at pick
  have twice : 2*(∑ v ∈ S,P j v) ≤ ∑ u ∈ S, ∑ v ∈ S,P u v := by rw [rows]; linarith
  change (∑ i ∈ S,h i) - (∑ u ∈ S,∑ v ∈ S,P u v)/2 ≤ Y
  by_cases good : j ∈ B
  · have eqrow : (∑ i ∈ S.filter (· ∉ B),h i) = ∑ i ∈ S,P j i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases bi : i∈B
      · simp [P,pairCharge,good,bi]
      · have ne : j≠i := fun e => bi (e ▸ good)
        simp [P,pairCharge,good,bi,ne,min_eq_right (big _ hi)]
    have parts := Finset.sum_filter_add_sum_filter_not S (fun i => i∈B) h
    linarith
  · have eqrow : (∑ i ∈ S.erase j,h i) = ∑ i ∈ S.erase j,P j i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [P,pairCharge,good,(Finset.ne_of_mem_erase hi).symm,min_eq_right (big i (Finset.mem_of_mem_erase hi))]
    have parts := Finset.sum_erase_add S h hj
    linarith [paid j hj]

end
end HadwigerNelson.Forest

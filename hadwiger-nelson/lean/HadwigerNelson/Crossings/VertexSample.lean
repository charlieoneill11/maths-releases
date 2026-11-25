import HadwigerNelson.Crossings.Parameters
import HadwigerNelson.Crossings.Subsets
import Mathlib.Tactic.Positivity

/-! Sum the linear drawing bound over all induced drawings on k vertices. -/
namespace HadwigerNelson.Crossings
open Finset
noncomputable section

theorem vertex_sample_bound (facts : CitedFacts) {n m k : ℕ} (G : Graph n m)
    (simple : G.IsSimple) (hk : 4 ≤ k) (hkn : k ≤ n)
    (count : ∀ W : Finset (Fin n), W.card ≤ k →
      (((univ : Finset (Fin n)).powersetCard k).filter fun S ↦ W ⊆ S).card =
        (n-W.card).choose (k-W.card))
    (pairs : (((n-2).choose (k-2) : ℕ) : ℝ) = (n.choose k : ℝ)*pairProbability n k)
    (quads : (((n-4).choose (k-4) : ℕ) : ℝ) = (n.choose k : ℝ)*fourProbability n k) :
    sampledLower n k m ≤ crossingNumber G := by
  classical
  obtain ⟨D,good,optimal⟩ := facts.attained G simple
  let Ω := (univ : Finset (Fin n)).powersetCard k
  let C := events D (good_finite good)
  let survive (V : Finset (Fin n)) (p : Fin m × Fin m × Plane) :=
    ends G p.1 ⊆ V ∧ ends G p.2.1 ⊆ V
  let crossings (V : Finset (Fin n)) := (C.filter (survive V)).card
  have totalE : (∑ V ∈ Ω, (keptEdges G V).card) = m * (n-2).choose (k-2) := by
    unfold keptEdges
    rw [sum_filter_card]
    have each (e : Fin m) : (Ω.filter fun V ↦ ends G e ⊆ V).card = (n-2).choose (k-2) := by
      simpa using count (ends G e) (by simp; omega)
    simp_rw [each]
    simp
  have totalC : (∑ V ∈ Ω, crossings V) = D.crossingCount * (n-4).choose (k-4) := by
    unfold crossings
    rw [sum_filter_card]
    calc
      _ = ∑ _p ∈ C, (n-4).choose (k-4) := by
        apply Finset.sum_congr rfl
        intro p hp
        have four := four_ends D good p ((mem_events _ _ _).mp hp)
        have i := count (ends G p.1 ∪ ends G p.2.1) (by omega)
        simpa only [Finset.union_subset_iff, four, survive] using i
      _ = _ := by simp [C]
  have localBound (V : Finset (Fin n)) (hV : V ∈ Ω) :
      6 * ((keptEdges G V).card : ℝ) - (266/9 : ℝ)*(k-2 : ℝ) ≤ crossings V := by
    have size := (mem_powersetCard.mp hV).2
    let s := induced G V size
    have lo := improved_lower facts s.graph (s.simple simple) (by omega)
    have le := facts.le_drawing s.graph (s.simple simple) (s.drawing D) (s.finite D (good_finite good))
    have bound := s.count_le_filter D (good_finite good) (fun e ↦ ends G e ⊆ V) (induced_keeps G V size)
    change (s.drawing D).crossingCount ≤ crossings V at bound
    have a : 54 * ((keptEdges G V).card : ℝ) - 266 * ((k : ℝ)-2) ≤ 9*(crossingNumber s.graph : ℝ) := by exact_mod_cast lo
    have b : (crossingNumber s.graph : ℝ) ≤ crossings V := by exact_mod_cast le.trans bound
    linarith
  have total := sum_le_sum localBound
  rw [sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at total
  have totEr : (∑ V ∈ Ω, ((keptEdges G V).card : ℝ)) = (m:ℝ)*((n-2).choose (k-2) : ℝ) := by exact_mod_cast totalE
  have totCr : (∑ V ∈ Ω, (crossings V : ℝ)) = (D.crossingCount:ℝ)*((n-4).choose (k-4) : ℝ) := by exact_mod_cast totalC
  have om : Ω.card = n.choose k := by simp [Ω,Finset.card_powersetCard]
  rw [totEr,totCr,pairs,quads,om,optimal] at total
  have positive : (0:ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  apply (div_le_iff₀ (fourProbability_pos hk hkn)).mpr
  apply (le_of_mul_le_mul_left _ positive)
  nlinarith only [total]

end
end HadwigerNelson.Crossings

import Chowla.Model.MatchingSum
import Chowla.EnclosureProofs

namespace Chowla

open scoped BigOperators

private theorem rectangle_profiles (ws : List ℝ) :
    ∀ f ∈ ws.map rectangle, IsProfile f := by
  intro f hf
  obtain ⟨w, _, rfl⟩ := List.mem_map.1 hf
  exact rectangle_isProfile w

/-- The marked profile occurs linearly in the contraction sum. -/
theorem crossMatchingSum_add {h g : FourierProfile} (hh : IsProfile h) (hg : IsProfile g)
    (A B : List ℝ) :
    crossMatchingSum (h + g) A B = crossMatchingSum h A B + crossMatchingSum g A B := by
  classical
  simp only [crossMatchingSum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro P _
  simp only [
    cumulant_add_head hh hg _ (rectangle_profiles _),
    cumulant_add_head hh hg [] (by simp)]
  simp only [show ∀ a : ℝ, cumulant [h + g, rectangle a] =
      cumulant [h, rectangle a] + cumulant [g, rectangle a] from fun a =>
        cumulant_add_head hh hg [rectangle a] (rectangle_profiles [a]),
    mul_add, Finset.sum_add_distrib]
  ring

theorem crossMatchingSum_const_mul (h : FourierProfile) (c : ℝ) (A B : List ℝ) :
    crossMatchingSum (fun u => c * h u) A B = c * crossMatchingSum h A B := by
  classical
  simp only [crossMatchingSum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P _
  simp only [cumulant_const_mul_head]
  simp only [mul_add, mul_left_comm _ c, Finset.mul_sum]

end Chowla

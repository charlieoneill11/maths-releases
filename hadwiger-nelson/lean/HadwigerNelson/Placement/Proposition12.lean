import HadwigerNelson.Placement.AngularIntegral
import HadwigerNelson.Placement.Bin
import HadwigerNelson.Placement.Quadrants

/-! The normalized real conclusion of the verified angular-bin method in Proposition 12. -/

open MeasureTheory Set HadwigerNelson.Wave
open scoped BigOperators

namespace HadwigerNelson.Placement

/-- The checker supplies nonnegative area upper bounds (in physical area units) on every bin.
This theorem places the resulting upper bound on the actual random-placement probability. -/
theorem meanMonoProb_of_bins (W : Datum) (N : ℕ) (hN : 0 < N) (area : ℕ → ℝ)
    (harea : ∀ j < N, 0 ≤ area j)
    (hcover : ∀ j < N, ∀ θ ∈ Icc (binEdge N j) (binEdge N (j+1)),
      W.x*H*directionalMonoProb W (point (Real.cos θ) (Real.sin θ)) ≤ area j) :
    meanMonoProb W ≤ (2 / (Real.pi * W.x * H)) *
      ∑ j ∈ Finset.range N, area j * (2*(N:ℝ)/((N:ℝ)^2+(j:ℝ)^2)) := by
  let p := fun θ ↦ directionalMonoProb W (point (Real.cos θ) (Real.sin θ))
  have hb := halfAngleIntegral_le N hN (fun θ ↦ (W.x*H)*p θ) area
    (fun j _ ↦ (intervalIntegrable_direction W _ _).const_mul _) harea hcover
  rw [intervalIntegral.integral_const_mul] at hb
  have hx : 0 < W.x := by linarith [W.x_bounds.1]
  have hn : 0 ≤ 2 / (Real.pi*W.x*H) := div_nonneg (by norm_num) (mul_pos (mul_pos Real.pi_pos hx) H_pos).le
  have z : 2 / (Real.pi*W.x*H) * (W.x*H) = 2/Real.pi := by field_simp [hx.ne',H_pos.ne',Real.pi_pos.ne']
  rw [meanMonoProb_quadrant, ← z, mul_assoc]
  exact mul_le_mul_of_nonneg_left hb hn

/-- The numerical checker can replace π in the denominator by any positive certified lower
bound, including the sharper rational bound used for the complete wave. -/
theorem meanMonoProb_of_bins_lower_pi (W : Datum) (N : ℕ) (hN : 0 < N) (area : ℕ → ℝ)
    (harea : ∀ j < N, 0 ≤ area j)
    (hcover : ∀ j < N, ∀ θ ∈ Icc (binEdge N j) (binEdge N (j+1)),
      W.x*H*directionalMonoProb W (point (Real.cos θ) (Real.sin θ)) ≤ area j)
    (lo : ℝ) (hpos : 0 < lo) (hlo : lo ≤ Real.pi) :
    meanMonoProb W ≤ (2 / (lo * W.x * H)) *
      ∑ j ∈ Finset.range N, area j * (2*(N:ℝ)/((N:ℝ)^2+(j:ℝ)^2)) := by
  apply (meanMonoProb_of_bins W N hN area harea hcover).trans
  have hx : 0 < W.x := by linarith [W.x_bounds.1]
  apply mul_le_mul_of_nonneg_right
  · exact div_le_div_of_nonneg_left (by norm_num) (mul_pos (mul_pos hpos hx) H_pos)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlo hx.le) H_pos.le)
  · apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (harea j (Finset.mem_range.mp hj)) (by positivity)

end HadwigerNelson.Placement

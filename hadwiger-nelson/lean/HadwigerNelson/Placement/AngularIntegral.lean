import HadwigerNelson.Arithmetic.Angle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Summing the first-quadrant slice majorants in Proposition 12. -/

open MeasureTheory Set
open scoped BigOperators

namespace HadwigerNelson.Placement

noncomputable section

/-- The left endpoint of the `j`-th bin, in radians. -/
def binEdge (N j : ℕ) : ℝ := 2 * Real.arctan ((j : ℝ) / N)

theorem binEdge_mono (N j : ℕ) : binEdge N j ≤ binEdge N (j+1) := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.arctan_mono
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.le_succ j

/-- Exact trigonometric range in a first-quadrant bin, before rounding its four endpoints. -/
theorem bin_component_bounds {N j : ℕ} (hN : 0 < N) (hj : j < N) {θ : ℝ}
    (hθ : θ ∈ Icc (binEdge N j) (binEdge N (j+1))) :
    Real.cos θ ∈ Icc (Arithmetic.rayX (((j:ℝ)+1)/N)) (Arithmetic.rayX ((j:ℝ)/N)) ∧
    Real.sin θ ∈ Icc (Arithmetic.rayY ((j:ℝ)/N)) (Arithmetic.rayY (((j:ℝ)+1)/N)) := by
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hn : 0 ≤ binEdge N j := by
    unfold binEdge
    apply mul_nonneg (by norm_num) (Real.arctan_nonneg.mpr (div_nonneg (Nat.cast_nonneg _) hNr.le))
  have hl : binEdge N (j+1) ≤ Real.pi/2 := by
    have ht : ((j+1 : ℕ):ℝ)/N ≤ 1 := (div_le_one hNr).2 (by exact_mod_cast Nat.succ_le_of_lt hj)
    have ha := Real.arctan_mono ht
    rw [Real.arctan_one] at ha
    dsimp [binEdge]; linarith
  have hpos := hn.trans hθ.1
  have hhi := hθ.2.trans hl
  have c (k : ℕ) : Real.cos (binEdge N k) = Arithmetic.rayX ((k:ℝ)/N) := Arithmetic.cos_two_arctan _
  have d (k : ℕ) : Real.sin (binEdge N k) = Arithmetic.rayY ((k:ℝ)/N) := Arithmetic.sin_two_arctan _
  have h1 := Real.cos_le_cos_of_nonneg_of_le_pi hpos (hl.trans (by linarith [Real.pi_pos])) hθ.2
  have h2 := Real.cos_le_cos_of_nonneg_of_le_pi hn (hhi.trans (by linarith [Real.pi_pos])) hθ.1
  have h3 := Real.sin_le_sin_of_le_of_le_pi_div_two (show -(Real.pi/2) ≤ binEdge N j by linarith [Real.pi_pos]) hhi hθ.1
  have h4 := Real.sin_le_sin_of_le_of_le_pi_div_two (show -(Real.pi/2) ≤ θ by linarith [Real.pi_pos]) hl hθ.2
  simpa [c,d] using And.intro (And.intro h1 h2) (And.intro h3 h4)

/-- Any array of nonnegative certified upper bounds on the angular bins gives a bound for
this integral. A certified zero on a block may consequently serve for each of its bins. -/
theorem halfAngleIntegral_le (N : ℕ) (hN : 0 < N) (f : ℝ → ℝ) (area : ℕ → ℝ)
    (hint : ∀ j < N, IntervalIntegrable f volume (binEdge N j) (binEdge N (j+1)))
    (harea : ∀ j < N, 0 ≤ area j)
    (hbound : ∀ j < N, ∀ θ ∈ Icc (binEdge N j) (binEdge N (j+1)), f θ ≤ area j) :
    (∫ θ in 0..Real.pi/2, f θ) ≤
      ∑ j ∈ Finset.range N, area j * (2 * (N : ℝ) / ((N : ℝ)^2 + (j : ℝ)^2)) := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have first : binEdge N 0 = 0 := by simp [binEdge]
  have last : binEdge N N = Real.pi / 2 := by simp [binEdge, hNr, Real.arctan_one] <;> ring
  rw [← first, ← last, ← intervalIntegral.sum_integral_adjacent_intervals hint]
  refine Finset.sum_le_sum (fun j hj ↦ ?_)
  have hj' := Finset.mem_range.mp hj
  have hwidth := Arithmetic.arctan_bin_le (N : ℤ) (j : ℤ) (by exact_mod_cast hN)
    (Int.natCast_nonneg _)
  push_cast at hwidth
  have hw : binEdge N (j+1) - binEdge N j ≤ 2 * (N : ℝ) / ((N : ℝ)^2 + (j : ℝ)^2) := by
    simpa only [binEdge, Nat.cast_add, Nat.cast_one, mul_sub] using hwidth
  calc
    _ ≤ ∫ _θ in binEdge N j..binEdge N (j+1), area j :=
      intervalIntegral.integral_mono_on (binEdge_mono N j) (hint j hj')
        intervalIntegrable_const (hbound j hj')
    _ = area j * (binEdge N (j+1) - binEdge N j) := by simp only [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (harea j hj')

end
end HadwigerNelson.Placement

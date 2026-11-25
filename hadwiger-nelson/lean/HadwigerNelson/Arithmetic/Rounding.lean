import HadwigerNelson.Arithmetic.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Directed integer arithmetic for the polygon and angular enclosures. The area
returned by the polygon integrator is in units of twice the geometric area. -/

namespace HadwigerNelson.Arithmetic

theorem floorDiv_le_real (a : Int) {b : Int} (hb : 0 < b) :
    ((a / b : Int) : ℝ) ≤ (a : ℝ) / b := by
  apply (le_div_iff₀ (show (0:ℝ) < b by exact_mod_cast hb)).2
  exact_mod_cast Int.ediv_mul_le a (ne_of_gt hb)

theorem real_lt_floorDiv_add_one (a : Int) {b : Int} (hb : 0 < b) :
    (a : ℝ) / b < ((a / b : Int) : ℝ) + 1 := by
  apply (div_lt_iff₀ (show (0:ℝ) < b by exact_mod_cast hb)).2
  have h : a < (a/b + 1)*b := by
    simpa only [Int.add_mul, Int.one_mul, Int.mul_comm b (a/b)] using Int.lt_mul_ediv_self_add (x := a) hb
  exact_mod_cast h

theorem real_le_ceilDiv (a : Int) {b : Int} (hb : 0 < b) :
    (a : ℝ) / b ≤ (ceilDiv a b : ℝ) := by
  simpa [ceilDiv, neg_div] using neg_le_neg (floorDiv_le_real (-a) hb)

theorem ceilDiv_lt_real_add_one (a : Int) {b : Int} (hb : 0 < b) :
    (ceilDiv a b : ℝ) < (a : ℝ) / b + 1 := by
  have h := real_lt_floorDiv_add_one (-a) hb
  simp only [Int.cast_neg, neg_div] at h
  simp only [ceilDiv, Int.cast_neg]
  linarith

/-- C++ signed quotient truncates toward zero in the fixed-point complex product. -/
theorem tdiv_error (a : Int) {b : Int} (hb : 0 < b) :
    |((a.tdiv b : Int) : ℝ) - (a : ℝ)/b| < 1 := by
  rcases le_total 0 a with ha | ha
  · rw [Int.tdiv_eq_ediv_of_nonneg ha, abs_of_nonpos (sub_nonpos.mpr (floorDiv_le_real a hb))]
    linarith [real_lt_floorDiv_add_one a hb]
  · have he : a.tdiv b = ceilDiv a b := by
      dsimp [ceilDiv]
      rw [← Int.tdiv_eq_ediv_of_nonneg (Int.neg_nonneg_of_nonpos ha), Int.neg_tdiv, neg_neg]
    rw [he, abs_of_nonneg (sub_nonneg.mpr (real_le_ceilDiv a hb))]
    linarith [ceilDiv_lt_real_add_one a hb]

/-- The affine function through two specified points, evaluated at height z. -/
noncomputable def linearAt (z₀ w₀ z₁ w₁ z : ℝ) : ℝ :=
  w₀ + (w₁-w₀)*(z-z₀)/(z₁-z₀)

theorem interpUp_spec (z₀ w₀ z₁ w₁ z : Int) (hz : z₀ < z₁) :
    linearAt z₀ w₀ z₁ w₁ z ≤ (interpUp z₀ w₀ z₁ w₁ z : ℝ) := by
  have h := real_le_ceilDiv ((w₁-w₀)*(z-z₀)) (b := z₁-z₀) (sub_pos.mpr hz)
  simpa [linearAt,interpUp] using add_le_add_right h (w₀ : ℝ)

theorem interpDown_spec (z₀ w₀ z₁ w₁ z : Int) (hz : z₀ < z₁) :
    (interpDown z₀ w₀ z₁ w₁ z : ℝ) ≤ linearAt z₀ w₀ z₁ w₁ z := by
  have h := floorDiv_le_real ((w₁-w₀)*(z-z₀)) (b := z₁-z₀) (sub_pos.mpr hz)
  simpa [linearAt,interpDown] using add_le_add_right h (w₀ : ℝ)

/-- Twice the exact integral of the positive part of a line segment, as a
function of its two endpoint values and horizontal width. -/
noncomputable def positiveArea2 (u v width : ℝ) : ℝ :=
  let a := min u v
  let b := max u v
  if b ≤ 0 then 0 else if 0 ≤ a then (a+b)*width else b*b*width/(b-a)

theorem positiveArea2Up_spec (u v width : Int) :
    positiveArea2 u v width ≤ (positiveArea2Up u v width : ℝ) := by
  simp only [positiveArea2,positiveArea2Up, ← Int.cast_min, ← Int.cast_max]
  split_ifs with hb hb' ha ha'
  all_goals try norm_cast at *
  all_goals try simp_all
  any_goals
    have hden : 0 < max u v - min u v := by omega
    exact_mod_cast real_le_ceilDiv ((max u v)*(max u v)*width) hden

theorem positiveArea2Up_full (u v width : Int) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    positiveArea2Up u v width = (u+v)*width := by
  rcases le_total u v with h | h
  · simp only [positiveArea2Up, min_eq_left h, max_eq_right h, if_pos hu]
    split
    · have : u = 0 ∧ v = 0 := by omega
      simp [this.1, this.2]
    · rfl
  · simp only [positiveArea2Up, min_eq_right h, max_eq_left h, if_pos hv]
    split
    · have : u = 0 ∧ v = 0 := by omega
      simp [this.1, this.2]
    · rw [add_comm]

end HadwigerNelson.Arithmetic

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Invariance of the fundamental rectangle used for the staggered wave lattice. -/

open MeasureTheory

namespace HadwigerNelson.Placement

noncomputable section

/-- Integrating one full period removes every translate of the argument. -/
theorem integral_translate_period {f : ℝ → ℝ} {T : ℝ} (h : Function.Periodic f T) (u : ℝ) :
    (∫ x in 0..T, f (x + u)) = ∫ x in 0..T, f x := by
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm T u] using h.intervalIntegral_add_eq u 0

/-- For a periodic observable, reflecting around any point preserves the full-period integral. -/
theorem integral_reverse_period {f : ℝ → ℝ} {T : ℝ} (h : Function.Periodic f T) (u : ℝ) :
    (∫ x in 0..T, f (u - x)) = ∫ x in 0..T, f x := by
  rw [intervalIntegral.integral_comp_sub_left]
  simpa using h.intervalIntegral_add_eq (u-T) 0

theorem staggered_outer_period (f : ℝ → ℝ → ℝ) (U V shear : ℝ)
    (hu : ∀ x y, f (x + U) (y + shear) = f x y)
    (hv : ∀ x, Function.Periodic (f x) V) :
    Function.Periodic (fun x ↦ ∫ y in 0..V, f x y) U := by
  intro x
  calc
    _ = ∫ y in 0..V, f (x + U) (y + shear) := (integral_translate_period (hv _) _).symm
    _ = ∫ y in 0..V, f x y := by simp_rw [hu]

/-- In a rectangular fundamental domain with periods `(U, shear)` and `(0,V)`, vertical
integration removes the shear in the first period. -/
theorem integral_staggered_translate (f : ℝ → ℝ → ℝ) (U V shear a b : ℝ)
    (hu : ∀ x y, f (x + U) (y + shear) = f x y)
    (hv : ∀ x, Function.Periodic (f x) V) :
    (∫ x in 0..U, ∫ y in 0..V, f (x + a) (y + b)) =
      ∫ x in 0..U, ∫ y in 0..V, f x y := by
  simp_rw [integral_translate_period (hv _) b]
  exact integral_translate_period (staggered_outer_period f U V shear hu hv) a

end
end HadwigerNelson.Placement

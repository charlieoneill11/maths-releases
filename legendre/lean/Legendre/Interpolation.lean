import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

namespace Legendre

open Set

private theorem convex_add_parabola {f : ℝ → ℝ} {a b C : ℝ} (hf : ContDiff ℝ 2 f)
    (h₂ : ∀ x ∈ Icc a b, -C ≤ deriv (deriv f) x) :
    ConvexOn ℝ (Icc a b) (fun x ↦ C / 2 * x ^ 2 + f x) := by
  have hf₁ := hf.differentiable (by norm_num)
  have hf₂ := hf.differentiable_deriv_two
  let g : ℝ → ℝ := fun x ↦ C / 2 * x ^ 2 + f x
  have hg (x : ℝ) : HasDerivAt g (C * x + deriv f x) x := by
    convert (((hasDerivAt_id x).pow 2).const_mul (C / 2)).add (hf₁ x).hasDerivAt using 1
    simp only [Nat.cast_ofNat, id_eq, mul_one]
    ring
  have hEq : deriv g = fun x ↦ C * x + deriv f x := funext fun x ↦ (hg x).deriv
  refine convexOn_of_deriv2_nonneg' (convex_Icc a b)
    (fun x _ ↦ (hg x).differentiableAt.differentiableWithinAt) ?_ ?_
  · rw [hEq]
    exact (show Differentiable ℝ (fun x ↦ C * x + deriv f x) from
      ((differentiable_const C).mul differentiable_id).add hf₂).differentiableOn
  · intro x hx
    change 0 ≤ deriv (deriv g) x
    rw [hEq]
    have hder : HasDerivAt (fun y ↦ C * y + deriv f y) (C * 1 + deriv (deriv f) x) x :=
      ((hasDerivAt_id x).const_mul C).add (hf₂ x).hasDerivAt
    rw [hder.deriv]
    linarith [h₂ x hx]

/-- A uniform second derivative bound controls the error of linear interpolation. -/
theorem linearInterpolation_error {f : ℝ → ℝ} {a b x C : ℝ} (hab : a < b)
    (hx : x ∈ Icc a b) (hf : ContDiff ℝ 2 f)
    (h₂ : ∀ y ∈ Icc a b, |deriv (deriv f) y| ≤ C) :
    |f x - ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b)| ≤
      C * (b - a) ^ 2 / 8 := by
  have hnonneg : 0 ≤ C := (abs_nonneg _).trans (h₂ x hx)
  have hpos : 0 < b - a := sub_pos.mpr hab
  have hcPlus := convex_add_parabola hf (fun y hy ↦ (abs_le.mp (h₂ y hy)).1)
  have hcMinus : ConvexOn ℝ (Icc a b) (fun y ↦ C / 2 * y ^ 2 + (-f) y) := by
    apply convex_add_parabola hf.neg
    intro y hy
    have hneg : deriv (-f) = -(deriv f) := deriv.neg'
    change -C ≤ deriv (deriv (-f)) y
    rw [hneg, deriv.neg]
    linarith [(abs_le.mp (h₂ y hy)).2]
  let u := (b - x) / (b - a)
  let v := (x - a) / (b - a)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hx.2) hpos.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hx.1) hpos.le
  have hsum : u + v = 1 := by
    dsimp only [u, v]
    field_simp
    ring
  have hcenter : u * a + v * b = x := by
    dsimp only [u, v]
    field_simp
    ring
  have hquad : u * a ^ 2 + v * b ^ 2 - x ^ 2 = (x - a) * (b - x) := by
    dsimp only [u, v]
    field_simp
    ring
  have hPlus := hcPlus.2 (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hu hv hsum
  have hMinus := hcMinus.2 (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hu hv hsum
  simp only [smul_eq_mul, hcenter, Pi.neg_apply] at hPlus hMinus
  have hcurvature : (C / 2) * (u * a ^ 2 + v * b ^ 2 - x ^ 2) ≤ C * (b - a) ^ 2 / 8 := by
    rw [hquad]
    have hwidth : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by
      nlinarith [sq_nonneg (2 * x - a - b)]
    calc
      _ ≤ (C / 2) * ((b - a) ^ 2 / 4) := mul_le_mul_of_nonneg_left hwidth (by positivity)
      _ = _ := by ring
  change |f x - (u * f a + v * f b)| ≤ _
  rw [abs_le]
  constructor <;> nlinarith only [hPlus, hMinus, hcurvature]

end Legendre

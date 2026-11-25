import Legendre.Interpolation
import Legendre.TwelveConstants

namespace Legendre

open MeasureTheory Set

private theorem affine_weights {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    0 ≤ (b - x) / (b - a) ∧ 0 ≤ (x - a) / (b - a) ∧
      (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
  have hp := sub_pos.mpr hab
  refine ⟨div_nonneg (sub_nonneg.mpr hx.2) hp.le, div_nonneg (sub_nonneg.mpr hx.1) hp.le, ?_⟩
  rw [← add_div, show b - x + (x - a) = b - a by ring, div_self hp.ne']

private theorem abs_le_affine_add {f : ℝ → ℝ} {a b x C : ℝ} (hab : a < b) (hx : x ∈ Icc a b)
    (hf : ContDiff ℝ 2 f) (h₂ : ∀ y ∈ Icc a b, |deriv (deriv f) y| ≤ C) :
    |f x| ≤ (b - x) / (b - a) * |f a| + (x - a) / (b - a) * |f b| + C * (b - a) ^ 2 / 8 := by
  obtain ⟨hu, hv, _⟩ := affine_weights hab hx
  let u := (b - x) / (b - a)
  let v := (x - a) / (b - a)
  let L := u * f a + v * f b
  have h := linearInterpolation_error hab hx hf h₂
  change |f x - L| ≤ _ at h
  have hL : |L| ≤ u * |f a| + v * |f b| := by
    unfold L
    exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul,
      abs_of_nonneg (show 0 ≤ u from hu), abs_of_nonneg (show 0 ≤ v from hv)])
  change |f x| ≤ u * |f a| + v * |f b| + _
  calc
    |f x| = |(f x - L) + L| := by rw [sub_add_cancel]
    _ ≤ |f x - L| + |L| := abs_add_le _ _
    _ ≤ _ := by linarith

private theorem max_sub_le_abs_of_same_sign {f : ℝ → ℝ} {a b x C m : ℝ}
    (hab : a < b) (hx : x ∈ Icc a b) (hf : ContDiff ℝ 2 f)
    (h₂ : ∀ y ∈ Icc a b, |deriv (deriv f) y| ≤ C)
    (hA : m ≤ |f a|) (hB : m ≤ |f b|)
    (hsgn : (0 ≤ f a ∧ 0 ≤ f b) ∨ (f a ≤ 0 ∧ f b ≤ 0)) :
    max 0 (m - C * (b - a) ^ 2 / 8) ≤ |f x| := by
  obtain ⟨hu, hv, hsum⟩ := affine_weights hab hx
  let u := (b - x) / (b - a)
  let v := (x - a) / (b - a)
  let L := u * f a + v * f b
  have hL : |L| = u * |f a| + v * |f b| := by
    unfold L
    rcases hsgn with hp | hn
    · rw [abs_of_nonneg (add_nonneg (mul_nonneg hu hp.1) (mul_nonneg hv hp.2)),
        abs_of_nonneg hp.1, abs_of_nonneg hp.2]
    · rw [abs_of_nonpos (add_nonpos (mul_nonpos_of_nonneg_of_nonpos hu hn.1)
        (mul_nonpos_of_nonneg_of_nonpos hv hn.2)), abs_of_nonpos hn.1, abs_of_nonpos hn.2]
      ring
  have hm : m ≤ |L| := by
    rw [hL, ← one_mul m, ← hsum, add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hA hu) (mul_le_mul_of_nonneg_left hB hv)
  have h := linearInterpolation_error hab hx hf h₂
  change |f x - L| ≤ _ at h
  have hL' : |L| ≤ |f x - L| + |f x| := by
    calc
      |L| = |(L - f x) + f x| := by rw [sub_add_cancel]
      _ ≤ |L - f x| + |f x| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm]
  exact max_le (abs_nonneg _) (by linarith)

private theorem integral_affine {a b A B E : ℝ} (hab : a < b) :
    (∫ x in a..b, (b - x) / (b - a) * A + (x - a) / (b - a) * B + E) =
      (b - a) * ((A + B) / 2 + E) := by
  have heq (x : ℝ) : (b - x) / (b - a) * A + (x - a) / (b - a) * B + E =
      (B - A) / (b - a) * x + (b * A - a * B) / (b - a) + E := by ring
  simp_rw [heq]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    integral_id, intervalIntegral.integral_const, intervalIntegral.integral_const,
    smul_eq_mul, smul_eq_mul]
  · field_simp [sub_ne_zero.mpr hab.ne']
    ring
  · exact continuous_const.mul continuous_id |>.intervalIntegrable _ _
  · exact intervalIntegrable_const
  · exact (show Continuous fun x : ℝ ↦ (B - A) / (b - a) * x + (b * A - a * B) / (b - a)
      by fun_prop).intervalIntegrable _ _
  · exact intervalIntegrable_const

theorem quadrature_mass_cell {f : ℝ → ℝ} {a b C A B : ℝ} (hab : a < b) (hf : ContDiff ℝ 2 f)
    (h₂ : ∀ y ∈ Icc a b, |deriv (deriv f) y| ≤ C) (hA : |f a| ≤ A) (hB : |f b| ≤ B) :
    (∫ x in a..b, |f x|) ≤ (b - a) * ((A + B) / 2 + C * (b - a) ^ 2 / 8) := by
  rw [← integral_affine hab]
  apply intervalIntegral.integral_mono_on hab.le (hf.continuous.abs.intervalIntegrable _ _)
    ((show Continuous fun x : ℝ ↦ (b - x) / (b - a) * A + (x - a) / (b - a) * B +
      C * (b - a) ^ 2 / 8 by fun_prop).intervalIntegrable _ _)
  intro x hx
  obtain ⟨hu, hv, _⟩ := affine_weights hab hx
  exact (abs_le_affine_add hab hx hf h₂).trans
    (add_le_add_left (add_le_add (mul_le_mul_of_nonneg_left hA hu)
      (mul_le_mul_of_nonneg_left hB hv)) _)

private theorem weighted_log_integrable {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f) :
    IntervalIntegrable (fun x ↦ |f x| * Real.log x) volume a b :=
  (intervalIntegral.intervalIntegrable_log' (a := a) (b := b)).continuousOn_mul hf.abs.continuousOn

theorem quadrature_log_cell_pos {f : ℝ → ℝ} {a b C A B : ℝ} (hab : a < b) (ha : 1 ≤ a)
    (hf : ContDiff ℝ 2 f) (h₂ : ∀ y ∈ Icc a b, |deriv (deriv f) y| ≤ C)
    (hA : |f a| ≤ A) (hB : |f b| ≤ B) :
    (∫ x in a..b, |f x| * Real.log x) ≤
      (max A B + C * (b - a) ^ 2 / 8) * ∫ x in a..b, Real.log x := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hab.le (weighted_log_integrable hf.continuous)
    ((intervalIntegral.intervalIntegrable_log' (a := a) (b := b)).const_mul _)
  intro x hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (ha.trans hx.1)
  obtain ⟨hu, hv, hsum⟩ := affine_weights hab hx
  have hA' : |f a| ≤ max A B := hA.trans (le_max_left _ _)
  have hB' : |f b| ≤ max A B := hB.trans (le_max_right _ _)
  have h := add_le_add (mul_le_mul_of_nonneg_left hA' hu) (mul_le_mul_of_nonneg_left hB' hv)
  rw [← add_mul, hsum, one_mul] at h
  exact mul_le_mul_of_nonneg_right ((abs_le_affine_add hab hx hf h₂).trans
    (add_le_add_left h _)) hlog

theorem quadrature_log_cell_neg {f : ℝ → ℝ} {a b C m : ℝ} (hab : a < b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hf : ContDiff ℝ 2 f) (h₂ : ∀ y ∈ Icc a b, |deriv (deriv f) y| ≤ C)
    (hA : m ≤ |f a|) (hB : m ≤ |f b|)
    (hsgn : (0 ≤ f a ∧ 0 ≤ f b) ∨ (f a ≤ 0 ∧ f b ≤ 0)) :
    (∫ x in a..b, |f x| * Real.log x) ≤
      max 0 (m - C * (b - a) ^ 2 / 8) * ∫ x in a..b, Real.log x := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hab.le (weighted_log_integrable hf.continuous)
    ((intervalIntegral.intervalIntegrable_log' (a := a) (b := b)).const_mul _)
  intro x hx
  exact mul_le_mul_of_nonpos_right (max_sub_le_abs_of_same_sign hab hx hf h₂ hA hB hsgn)
    (Real.log_nonpos (ha.trans hx.1) (hx.2.trans hb))

theorem quadrature_log_cell_nonpos {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (ha : 0 ≤ a) (hb : b ≤ 1) : (∫ x in a..b, |f x| * Real.log x) ≤ 0 := by
  have h := intervalIntegral.integral_nonneg (μ := volume) (f := fun x ↦ -(|f x| * Real.log x))
    hab.le fun _ hx ↦ neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _)
        (Real.log_nonpos (ha.trans hx.1) (hx.2.trans hb)))
  simpa only [intervalIntegral.integral_neg, neg_nonneg] using h

end Legendre

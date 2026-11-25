import HadwigerNelson.Stars.RealFourier.Character
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace HadwigerNelson.Stars
open MeasureTheory Set

/-- A pointwise lower bound on the interior gives the matching area lower
bound, including degenerate spans. -/
theorem span_mean_lower (g : ℝ → ℝ) {a b m r : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (lo : ∀ t ∈ Ioo a b, m-r ≤ g t) :
    (m-r)*(b-a) ≤ ∫ t in a..b, g t := by
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hab
    (intervalIntegrable_const (c := m-r)) hg lo
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm (b-a)] using h

/-- Replacing a bounded signed response by its midpoint on one span changes
its kth Fourier integral by at most the radius times the length of the span. -/
theorem span_moment_error_le (g : ℝ → ℝ) (k : ℕ) {a b m r : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (bound : ∀ t ∈ Ioo a b, |g t-m| ≤ r) :
    ‖(∫ t in a..b, (g t : ℂ) * anglePhase t^k) -
      (m : ℂ) * (∫ t in a..b, anglePhase t^k)‖ ≤ r*(b-a) := by
  have cont : Continuous (fun t => anglePhase t^k) := anglePhase_continuous.pow k
  have gi : IntervalIntegrable (fun t => (g t : ℂ)) volume a b := ⟨hg.1.ofReal,hg.2.ofReal⟩
  erw [← intervalIntegral.integral_const_mul (μ := volume) (a := a) (b := b) (m : ℂ) (fun t => anglePhase t^k),
    ← intervalIntegral.integral_sub
    (gi.mul_continuousOn cont.continuousOn) ((cont.intervalIntegrable a b).const_mul (m:ℂ))]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const_ae
    (a := a) (b := b) (C := r)
    (f := fun t => (g t : ℂ)*anglePhase t^k - (m : ℂ)*anglePhase t^k) (by
      filter_upwards [Measure.ae_ne volume b] with t hne ht
      rw [uIoc_of_le hab] at ht
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        norm_pow, norm_anglePhase, one_pow, mul_one]
      exact bound t ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using h

end HadwigerNelson.Stars

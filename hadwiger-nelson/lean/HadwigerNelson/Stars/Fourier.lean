import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Norm

/-! The magnitude of a Fourier coefficient is bounded by the L¹ norm, as
used for the signed angular response in Lemma 21. -/

open MeasureTheory

namespace HadwigerNelson.Stars

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Unit-modulus characters cannot increase the L¹ mass of a Fourier coefficient. -/
theorem fourier_norm_le (D : Ω → ℝ) (χ : Ω → ℂ) (unit : ∀ ω, ‖χ ω‖ = 1) :
    ‖∫ ω, (D ω : ℂ) * χ ω ∂μ‖ ≤ ∫ ω, |D ω| ∂μ := by
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, unit, mul_one] using
    norm_integral_le_integral_norm (μ := μ) (fun ω => (D ω : ℂ) * χ ω)

end HadwigerNelson.Stars

import Chowla.VariationalSmoothing
import Chowla.Claims
import Mathlib.Analysis.Fourier.Convolution

namespace Chowla

open MeasureTheory
open scoped Convolution FourierTransform SchwartzMap

private theorem complexProfile_integrable {h : FourierProfile} (hh : Integrable h) :
    Integrable (fun u : ℝ => (h u : ℂ)) :=
  Complex.ofRealCLM.integrable_comp hh

private theorem even_complex_inverseProfile {h : FourierProfile} (hh : Function.Even h) :
    Function.Even (𝓕⁻ (fun u : ℝ => (h u : ℂ))) := by
  intro x
  have heq : (fun u : ℝ => (h u : ℂ)) ∘ (LinearIsometryEquiv.neg ℝ (E := ℝ)) =
      (fun u : ℝ => (h u : ℂ)) := by
    funext u
    change (h (-u) : ℂ) = (h u : ℂ)
    rw [hh u]
  have h := Real.fourierInv_comp_linearIsometry
    (LinearIsometryEquiv.neg ℝ (E := ℝ)) (fun u : ℝ => (h u : ℂ)) x
  rw [heq] at h
  exact h.symm

private theorem complex_inverseProfile_im {h : FourierProfile}
    (he : Function.Even h) (hh : Integrable h) (x : ℝ) :
    (𝓕⁻ (fun u : ℝ => (h u : ℂ)) x).im = 0 := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  let φ : ℝ → ℂ := fun u => Complex.exp (↑(-2 * Real.pi * u * (-x)) * Complex.I) • (h u : ℂ)
  have hφ : Integrable φ := by
    unfold φ
    apply Integrable.mono (complexProfile_integrable hh)
    · exact ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.smul
        (complexProfile_integrable hh).aestronglyMeasurable)
    · filter_upwards with u
      simp [Complex.norm_exp]
  change Complex.imCLM (∫ u : ℝ, φ u) = 0
  rw [← Complex.imCLM.integral_comp_comm hφ]
  have hodd (u : ℝ) : Complex.imCLM (φ (-u)) = -(Complex.imCLM (φ u)) := by
    simp only [φ, Complex.imCLM_apply, smul_eq_mul, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, mul_zero, zero_add, Complex.exp_im, Complex.mul_I_re,
      neg_zero, Real.exp_zero, one_mul, Complex.I_re, Complex.I_im, mul_one, add_zero]
    rw [he u, show -2 * Real.pi * (-u) * (-x) = -(-2 * Real.pi * u * (-x)) by ring,
      Real.sin_neg, neg_mul]
  have heq : (∫ u : ℝ, Complex.imCLM (φ u)) = -(∫ u : ℝ, Complex.imCLM (φ u)) := by
    calc
      _ = ∫ u : ℝ, Complex.imCLM (φ (-u)) :=
        (integral_neg_eq_self (f := fun u : ℝ => Complex.imCLM (φ u)) volume).symm
      _ = ∫ u : ℝ, -(Complex.imCLM (φ u)) :=
        integral_congr_ae (Filter.Eventually.of_forall hodd)
      _ = _ := integral_neg _
  linarith

theorem ofReal_inverseProfile {h : FourierProfile} (hh : IsProfile h) (x : ℝ) :
    (inverseProfile h x : ℂ) = 𝓕⁻ (fun u : ℝ => (h u : ℂ)) x := by
  apply Complex.ext
  · simp [inverseProfile]
  · simp [complex_inverseProfile_im hh.2.1 (integrable_of_isProfile hh)]

theorem inverseProfile_zero {h : FourierProfile} (hh : IsProfile h) :
    inverseProfile h 0 = ∫ u : ℝ, h u := by
  unfold inverseProfile
  rw [Real.fourierInv_eq_fourier_neg, neg_zero, Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
  change Complex.reCLM (∫ u : ℝ, (h u : ℂ)) = _
  rw [← Complex.reCLM.integral_comp_comm (complexProfile_integrable (integrable_of_isProfile hh))]
  simp

private noncomputable def smoothComplexProfile (h : FourierProfile) (hC : ContDiff ℝ (↑(⊤ : ℕ∞)) h)
    (hK : HasCompactSupport h) : 𝓢(ℝ, ℂ) :=
  (hK.toSchwartzMap hC).postcompCLM Complex.ofRealCLM

/-- The inverse of a smooth, compactly supported profile is a real Schwartz test. -/
noncomputable def MomentTest.ofProfile (h : FourierProfile) (hh : IsProfile h)
    (hC : ContDiff ℝ (↑(⊤ : ℕ∞)) h) : MomentTest := by
  let complex := smoothComplexProfile h hC hh.2.2.2
  let f : 𝓢(ℝ, ℝ) := (𝓕⁻ complex).postcompCLM Complex.reCLM
  have hfun : ∀ x : ℝ, f x = inverseProfile h x := by
    intro x
    rw [show f x = Complex.reCLM ((𝓕⁻ complex) x) by rfl]
    simp only [inverseProfile, Complex.reCLM_apply]
    rw [congrFun (SchwartzMap.fourierInv_coe complex) x]
    rfl
  have hcomp : fourier (fun x => f x) = fun u => (h u : ℂ) := by
    unfold fourier
    have heq : (fun x : ℝ => (f x : ℂ)) = ((𝓕⁻ complex : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
      funext x
      rw [hfun, ofReal_inverseProfile hh]
      exact (congrFun (SchwartzMap.fourierInv_coe complex) x).symm
    rw [heq, ← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
    rfl
  refine ⟨f, fun x => ?_, ?_⟩
  · change f (-x) = f x
    rw [hfun, hfun, inverseProfile, inverseProfile]
    exact congrArg Complex.re (even_complex_inverseProfile hh.2.1 x)
  · rw [hcomp]
    exact hh.2.2.2.comp_left Complex.ofReal_zero

theorem MomentTest.ofProfile_apply (h : FourierProfile) (hh : IsProfile h)
    (hC : ContDiff ℝ (↑(⊤ : ℕ∞)) h) (x : ℝ) :
    (MomentTest.ofProfile h hh hC).toSchwartz x = inverseProfile h x := by
  change Complex.reCLM ((𝓕⁻ (smoothComplexProfile h hC hh.2.2.2)) x) = _
  rw [congrFun (SchwartzMap.fourierInv_coe _) x]
  rfl

theorem MomentTest.ofProfile_profile (h : FourierProfile) (hh : IsProfile h)
    (hC : ContDiff ℝ (↑(⊤ : ℕ∞)) h) :
    (MomentTest.ofProfile h hh hC).profile = h := by
  funext u
  unfold MomentTest.profile fourier
  have heq : (fun x : ℝ => ((MomentTest.ofProfile h hh hC).toSchwartz x : ℂ)) =
      ((𝓕⁻ (smoothComplexProfile h hC hh.2.2.2) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    funext x
    rw [MomentTest.ofProfile_apply, ofReal_inverseProfile hh]
    exact (congrFun (SchwartzMap.fourierInv_coe (smoothComplexProfile h hC hh.2.2.2)) x).symm
  rw [heq, ← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  rfl


private theorem complexProfile_convolve (h g : FourierProfile) (hh : IsProfile h)
    (hg : IsProfile g) (hgc : Continuous g) :
    (fun u : ℝ => (convolve h g u : ℂ)) =
      (fun u : ℝ => (h u : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun u : ℝ => (g u : ℂ)) := by
  funext x
  have hi : Integrable (fun t : ℝ => h t * g (x - t)) :=
    hg.2.2.2.convolutionExists_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (integrable_of_isProfile hh).locallyIntegrable hgc x
  rw [convolve_apply, convolution_def]
  change Complex.ofRealCLM (∫ t : ℝ, h t * g (x - t)) =
    ∫ t : ℝ, (h t : ℂ) * (g (x - t) : ℂ)
  rw [← Complex.ofRealCLM.integral_comp_comm hi]
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_mul]

/-- The two-profile products in the square expansion correspond to convolution. -/
theorem inverseProfile_convolve (h g : FourierProfile) (hh : IsProfile h) (hg : IsProfile g)
    (hhc : Continuous h) (hgc : Continuous g) (x : ℝ) :
    inverseProfile (convolve h g) x = inverseProfile h x * inverseProfile g x := by
  have heq : (inverseProfile (convolve h g) x : ℂ) =
      (inverseProfile h x : ℂ) * (inverseProfile g x : ℂ) := by
    rw [ofReal_inverseProfile (convolve_isProfile hh hg), ofReal_inverseProfile hh,
      ofReal_inverseProfile hg, complexProfile_convolve h g hh hg hgc]
    simp only [Real.fourierInv_eq_fourier_neg]
    exact Real.fourier_mul_convolution_eq
      (complexProfile_integrable (integrable_of_isProfile hh))
      (complexProfile_integrable (integrable_of_isProfile hg))
      (Complex.continuous_ofReal.comp hhc) (Complex.continuous_ofReal.comp hgc) (-x)
  exact_mod_cast heq

end Chowla

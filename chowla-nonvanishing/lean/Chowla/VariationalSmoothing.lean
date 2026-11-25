import Chowla.Model.Cumulants
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace Chowla

open Filter MeasureTheory Set
open scoped Topology Convolution NNReal

/-- Mass-preserving dilation by a positive real scale. -/
noncomputable def dilateProfile (scale : ℝ) (h : FourierProfile) : FourierProfile :=
  fun u => scale⁻¹ * h (u / scale)

noncomputable def smoothProfile (ρ : FourierProfile) (scale δ : ℝ) (h : FourierProfile) :
    FourierProfile :=
  convolve (dilateProfile scale h) (dilateProfile δ ρ)

theorem dilateProfile_isProfile (h : FourierProfile) (hh : IsProfile h)
    {scale : ℝ} (hs : 0 < scale) : IsProfile (dilateProfile scale h) := by
  have hsupp : HasCompactSupport (fun u : ℝ => h (u / scale)) := by
    simpa only [smul_eq_mul, ← div_eq_inv_mul] using hh.2.2.2.comp_smul (inv_ne_zero hs.ne')
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact measurable_const.mul (hh.1.comp (measurable_id.div_const scale))
  · intro x
    simp only [dilateProfile, neg_div, hh.2.1 (x / scale)]
  · obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hh.2.2.1
    refine isBounded_iff_forall_norm_le.mpr ⟨‖scale⁻¹‖ * C, ?_⟩
    rintro _ ⟨u, rfl⟩
    exact norm_mul_le _ _ |>.trans
      (mul_le_mul_of_nonneg_left (hC (h (u / scale)) ⟨u / scale, rfl⟩) (norm_nonneg _))
  · exact HasCompactSupport.mul_left hsupp

theorem dilateProfile_integral (h : FourierProfile) {scale : ℝ} (hs : 0 < scale) :
    (∫ u : ℝ, dilateProfile scale h u) = ∫ u : ℝ, h u := by
  simp only [dilateProfile, integral_const_mul, Measure.integral_comp_div, abs_of_pos hs,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]

theorem dilateProfile_radius {h : FourierProfile} {r scale : ℝ} (hh : HasRadiusAtMost h r)
    (hs : 0 < scale) : HasRadiusAtMost (dilateProfile scale h) (scale * r) := by
  refine ⟨mul_nonneg hs.le hh.1, ?_⟩
  have hm := Measure.quasiMeasurePreserving_smul (E := ℝ) volume (inv_ne_zero hs.ne')
  have hpre : ∀ᵐ u : ℝ ∂volume, u / scale ∉ Icc (-r) r → h (u / scale) = 0 := by
    simpa only [smul_eq_mul, ← div_eq_inv_mul] using hm.ae hh.2
  filter_upwards [hpre] with u hu hout
  have hdiv : u / scale ∉ Icc (-r) r := by
    intro hc
    apply hout
    exact ⟨by simpa [mul_comm, neg_mul] using (le_div_iff₀ hs).mp hc.1,
      by simpa [mul_comm] using (div_le_iff₀ hs).mp hc.2⟩
  simp [dilateProfile, hu hdiv]

theorem smoothProfile_isProfile (ρ h : FourierProfile) (hρ : IsProfile ρ)
    (hh : IsProfile h) {scale δ : ℝ} (hs : 0 < scale) (hδ : 0 < δ) :
    IsProfile (smoothProfile ρ scale δ h) :=
  convolve_isProfile (dilateProfile_isProfile h hh hs) (dilateProfile_isProfile ρ hρ hδ)

/-- The smoothing preserves integral and adds at most δ to the scaled radius. -/
theorem smoothProfile_properties (ρ h : FourierProfile) (scale δ : ℝ)
    (hρ : IsProfile ρ) (hρsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ)
    (hρsupport : HasRadiusAtMost ρ 1) (hρmass : (∫ u : ℝ, ρ u) = 1)
    (hh : IsProfile h) (hscale : 0 < scale) (hδ : 0 < δ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (smoothProfile ρ scale δ h) ∧
      (∫ u : ℝ, smoothProfile ρ scale δ h u) = (∫ u : ℝ, h u) ∧
      HasRadiusAtMost (smoothProfile ρ scale δ h) (scale * radius h + δ) := by
  have hp := dilateProfile_isProfile h hh hscale
  have hq := dilateProfile_isProfile ρ hρ hδ
  refine ⟨?_, ?_, ?_⟩
  · change ContDiff ℝ (↑(⊤ : ℕ∞))
      ((dilateProfile scale h) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (dilateProfile δ ρ))
    apply hq.2.2.2.contDiff_convolution_right
    · exact (integrable_of_isProfile hp).locallyIntegrable
    · unfold dilateProfile
      exact contDiff_const.mul (hρsmooth.comp (contDiff_id.div_const δ))
  · unfold smoothProfile
    rw [integral_convolve (integrable_of_isProfile hp) (integrable_of_isProfile hq),
      dilateProfile_integral _ hscale, dilateProfile_integral _ hδ, hρmass, mul_one]
  · simpa only [mul_one] using convolve_hasRadiusAtMost
      (dilateProfile_radius (hasRadiusAtMost_radius hh) hscale)
      (dilateProfile_radius hρsupport hδ)

theorem smoothProfile_sup (ρ h : FourierProfile) (hρ : IsProfile ρ)
    (hρnonneg : ∀ x, 0 ≤ ρ x) (hρmass : (∫ u : ℝ, ρ u) = 1)
    {scale δ B : ℝ} (hscale : 0 < scale) (hδ : 0 < δ)
    (hB : ∀ x : ℝ, |h x| ≤ B) (x : ℝ) :
    |smoothProfile ρ scale δ h x| ≤ scale⁻¹ * B := by
  have hρpositive (u : ℝ) : 0 ≤ dilateProfile δ ρ u :=
    mul_nonneg (inv_nonneg.mpr hδ.le) (hρnonneg (u / δ))
  have hm : profileL1 (dilateProfile δ ρ) = 1 := by
    unfold profileL1
    simp_rw [abs_of_nonneg (hρpositive _)]
    rw [dilateProfile_integral _ hδ, hρmass]
  unfold smoothProfile
  rw [convolve_comm]
  refine (abs_convolve_le_of_right_bound (C := scale⁻¹ * B)
    (integrable_of_isProfile (dilateProfile_isProfile ρ hρ hδ)) ?_ x).trans_eq ?_
  · intro u
    simp only [dilateProfile, abs_mul, abs_of_pos (inv_pos.mpr hscale)]
    exact mul_le_mul_of_nonneg_left (hB (u / scale)) (inv_nonneg.mpr hscale.le)
  · rw [hm, one_mul]

end Chowla

import Chowla.VariationalSmoothing
import Chowla.Model.Continuity
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Chowla

open Filter Function MeasureTheory Set
open scoped Convolution Topology

theorem dilateProfile_integrable {h : FourierProfile} (hh : Integrable h)
    {s : ℝ} (hs : 0 < s) : Integrable (dilateProfile s h) := by
  unfold dilateProfile
  exact (hh.comp_div hs.ne').const_mul _

theorem dilateProfile_profileL1 (h : FourierProfile) {s : ℝ} (hs : 0 < s) :
    profileL1 (dilateProfile s h) = profileL1 h := by
  simpa only [profileL1, dilateProfile, abs_mul, abs_of_pos (inv_pos.mpr hs)] using
    dilateProfile_integral (fun x => |h x|) hs

private theorem smoothProfile_sub_ae (ρ h g : FourierProfile) {s δ : ℝ}
    (hρ : Integrable ρ) (hh : Integrable h) (hg : Integrable g) (hs : 0 < s) (hδ : 0 < δ) :
    smoothProfile ρ s δ h - smoothProfile ρ s δ g =ᵐ[volume] smoothProfile ρ s δ (h - g) := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have h₁ := (dilateProfile_integrable hh hs).ae_convolution_exists L (dilateProfile_integrable hρ hδ)
  have h₂ := (dilateProfile_integrable hg hs).ae_convolution_exists L (dilateProfile_integrable hρ hδ)
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  change Integrable (fun t => dilateProfile s h t * dilateProfile δ ρ (x - t)) at hx₁
  change Integrable (fun t => dilateProfile s g t * dilateProfile δ ρ (x - t)) at hx₂
  simp only [Pi.sub_apply, smoothProfile, convolve_apply]
  rw [← integral_sub hx₁ hx₂]
  congr 1
  funext t
  simp only [dilateProfile, Pi.sub_apply, mul_sub, sub_mul]

theorem smoothProfile_contract (ρ h g : FourierProfile) {s δ : ℝ}
    (hρ : Integrable ρ) (hρnonneg : ∀ x, 0 ≤ ρ x) (hρmass : (∫ u : ℝ, ρ u) = 1)
    (hh : Integrable h) (hg : Integrable g) (hs : 0 < s) (hδ : 0 < δ) :
    profileL1 (smoothProfile ρ s δ h - smoothProfile ρ s δ g) ≤ profileL1 (h - g) := by
  have hmass : profileL1 ρ = 1 := by simpa only [profileL1, abs_of_nonneg (hρnonneg _)] using hρmass
  rw [show profileL1 (smoothProfile ρ s δ h - smoothProfile ρ s δ g) =
    profileL1 (smoothProfile ρ s δ (h - g)) from
      integral_congr_ae ((smoothProfile_sub_ae ρ h g hρ hh hg hs hδ).fun_comp abs)]
  exact (profileL1_convolve_le (dilateProfile_integrable (hh.sub hg) hs)
    (dilateProfile_integrable hρ hδ)).trans_eq (by rw [dilateProfile_profileL1 _ hs,
      dilateProfile_profileL1 _ hδ, hmass, mul_one])

private theorem tendsto_support_dilation (ρ : FourierProfile) (hρsupport : support ρ ⊆ Icc (-1) 1)
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => support (dilateProfile (δ n) ρ)) atTop (𝓝 0).smallSets := by
  rw [tendsto_smallSets_iff]
  intro U hU
  obtain ⟨ε, hε, hU⟩ := Metric.mem_nhds_iff.mp hU
  filter_upwards [hδlim.eventually (Iio_mem_nhds hε)] with n hn
  intro x hx
  apply hU
  have hx' : x / δ n ∈ Icc (-1 : ℝ) 1 := hρsupport (by
    rw [mem_support] at hx ⊢
    intro hz
    exact hx (by simp [dilateProfile, hz]))
  have hb : |x / δ n| ≤ 1 := abs_le.mpr hx'
  rw [abs_div, abs_of_pos (hδ n), div_le_iff₀ (hδ n), one_mul] at hb
  simpa [Metric.mem_ball, Real.dist_eq] using hb.trans_lt hn

theorem smoothProfile_tendsto_at (ρ g : FourierProfile)
    (hρnonneg : ∀ x, 0 ≤ ρ x) (hρmass : (∫ u : ℝ, ρ u) = 1)
    (hρsupport : support ρ ⊆ Icc (-1) 1) (hgm : Measurable g)
    {s δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n)
    (hslim : Tendsto s atTop (𝓝 1)) (hδlim : Tendsto δ atTop (𝓝 0))
    {x : ℝ} (hg : ContinuousAt g x) :
    Tendsto (fun n => smoothProfile ρ (s n) (δ n) g x) atTop (𝓝 (g x)) := by
  have hnc : ∀ᶠ n in atTop, ∀ b, 0 ≤ dilateProfile (δ n) ρ b := Eventually.of_forall fun n b =>
    mul_nonneg (inv_nonneg.mpr (hδ n).le) (hρnonneg _)
  have hm : ∀ᶠ n in atTop, ∫ b : ℝ, dilateProfile (δ n) ρ b = 1 :=
    Eventually.of_forall fun n => (dilateProfile_integral ρ (hδ n)).trans hρmass
  have he : ∀ᶠ n in atTop, AEStronglyMeasurable (dilateProfile (s n) g) :=
    Eventually.of_forall fun n =>
      (measurable_const.mul (hgm.comp (measurable_id.div_const (s n)))).aestronglyMeasurable
  have hxy : Tendsto (fun p : ℕ × ℝ => p.2 / s p.1) (atTop ×ˢ 𝓝 x) (𝓝 x) := by
    simpa only [div_one] using tendsto_snd.div (hslim.comp tendsto_fst) one_ne_zero
  have hcomp : Tendsto (uncurry fun n => dilateProfile (s n) g) (atTop ×ˢ 𝓝 x) (𝓝 (g x)) := by
    simpa only [dilateProfile, uncurry, inv_one, one_mul] using
      ((hslim.comp tendsto_fst).inv₀ one_ne_zero).mul (hg.tendsto.comp hxy)
  simp only [smoothProfile, convolve_comm (dilateProfile _ g)]
  exact convolution_tendsto_right hnc hm (tendsto_support_dilation ρ hρsupport hδ hδlim)
    he hcomp tendsto_const_nhds

private theorem smoothProfile_L1_tendsto_of_continuous (ρ g : FourierProfile)
    (hρ : IsProfile ρ) (hρnonneg : ∀ x, 0 ≤ ρ x) (hρmass : (∫ u : ℝ, ρ u) = 1)
    (hρsupport : support ρ ⊆ Icc (-1) 1) (hg : Continuous g) (hgk : HasCompactSupport g)
    {s δ : ℕ → ℝ} (hs : ∀ n, 0 < s n) (hδ : ∀ n, 0 < δ n)
    (hslim : Tendsto s atTop (𝓝 1)) (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => profileL1 (smoothProfile ρ (s n) (δ n) g - g)) atTop (𝓝 0) := by
  have hρradius : HasRadiusAtMost ρ 1 := ⟨by norm_num, Eventually.of_forall fun x hx =>
    notMem_support.mp (fun hm => hx (hρsupport hm))⟩
  obtain ⟨R, hR⟩ := (hgk.isCompact.isBounded).subset_closedBall (0 : ℝ)
  let r := max R 0
  have hr : 0 ≤ r := le_max_right _ _
  have hgr : HasRadiusAtMost g r := ⟨hr, Eventually.of_forall fun x hx => notMem_support.mp (by
    intro hx'
    apply hx
    have h := hR (subset_tsupport _ hx')
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
    exact abs_le.mp (h.trans (le_max_left _ _)))⟩
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp (hgk.isCompact_range hg).isBounded
  have hB' (x : ℝ) : |g x| ≤ B := hB _ ⟨x, rfl⟩
  have hB₀ : 0 ≤ B := (abs_nonneg _).trans (hB' 0)
  let A := Icc (-(2 * r + 1)) (2 * r + 1)
  let F := fun n x => |smoothProfile ρ (s n) (δ n) g x - g x|
  have hInt : Integrable (A.indicator fun _ => 3 * B : ℝ → ℝ) :=
    (integrableOn_const (measure_Icc_lt_top.ne : volume A ≠ ⊤)).integrable_indicator measurableSet_Icc
  have hgM := hg.measurable
  have hMeas : ∀ᶠ n in atTop, AEStronglyMeasurable (F n) := Eventually.of_forall fun n => by
    apply Measurable.aestronglyMeasurable
    apply continuous_abs.measurable.comp
    apply Measurable.sub _ hgM
    apply measurable_convolve
    · exact measurable_const.mul (hgM.comp (measurable_id.div_const (s n)))
    · exact measurable_const.mul (hρ.1.comp (measurable_id.div_const (δ n)))
  have hsclose := hslim.eventually (Ioo_mem_nhds (show (1 : ℝ) / 2 < 1 by norm_num)
    (show (1 : ℝ) < 2 by norm_num))
  have hδclose := hδlim.eventually (Iio_mem_nhds zero_lt_one)
  have hBound : ∀ᶠ n in atTop, ∀ᵐ x : ℝ ∂volume, ‖F n x‖ ≤ A.indicator (fun _ => 3 * B) x := by
    filter_upwards [hsclose, hδclose] with n hsn hδn
    have hsmall : s n * r + δ n ≤ 2 * r + 1 := by
      have hh := mul_le_mul_of_nonneg_right hsn.2.le hr
      linarith
    have hS : HasRadiusAtMost (smoothProfile ρ (s n) (δ n) g) (2 * r + 1) :=
      (convolve_hasRadiusAtMost (dilateProfile_radius hgr (hs n))
        (dilateProfile_radius hρradius (hδ n))).mono (by simpa only [mul_one] using hsmall)
    filter_upwards [hS.2, (hgr.mono (by linarith : r ≤ 2 * r + 1)).2] with x hx hxg
    by_cases hx' : x ∈ A
    · rw [indicator_of_mem hx']
      have hi : (s n)⁻¹ ≤ 2 := by
        apply (inv_le_iff_one_le_mul₀ (hs n)).2
        linarith only [hsn.1]
      have hBcalc : |smoothProfile ρ (s n) (δ n) g x| ≤ 2 * B :=
        (smoothProfile_sup ρ g hρ hρnonneg hρmass (hs n) (hδ n) hB' x).trans
          (mul_le_mul_of_nonneg_right hi hB₀)
      simp only [F, Real.norm_eq_abs, abs_abs]
      calc
        _ ≤ _ := abs_sub _ _
        _ ≤ 3 * B := by linarith only [hBcalc, hB' x]
    · simp [F, hx hx', hxg hx', hx']
  have hLim : ∀ᵐ x : ℝ ∂volume, Tendsto (fun n => F n x) atTop (𝓝 ((0 : ℝ → ℝ) x)) :=
    Eventually.of_forall fun x => by
      simpa [F] using ((smoothProfile_tendsto_at ρ g hρnonneg hρmass hρsupport hgM
        hδ hslim hδlim (x := x) hg.continuousAt).sub_const (g x)).abs
  simpa only [profileL1, Pi.sub_apply, Pi.zero_apply, integral_zero, F] using
    tendsto_integral_filter_of_dominated_convergence (A.indicator fun _ => 3 * B)
      hMeas hBound hInt hLim

/-- The Fourier smoothing converges to the original profile in integral of absolute value. -/
theorem smoothProfile_L1_tendsto (ρ h : FourierProfile)
    (hρ : IsProfile ρ) (hρnonneg : ∀ x, 0 ≤ ρ x) (hρmass : (∫ u : ℝ, ρ u) = 1)
    (hρsupport : support ρ ⊆ Icc (-1) 1) (hh : Integrable h)
    {s δ : ℕ → ℝ} (hs : ∀ n, 0 < s n) (hδ : ∀ n, 0 < δ n)
    (hslim : Tendsto s atTop (𝓝 1)) (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => profileL1 (smoothProfile ρ (s n) (δ n) h - h)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε' : 0 < ε / 3 := by positivity
  obtain ⟨g, hgk, hgap, hgc, hg⟩ := (memLp_one_iff_integrable.2 hh).exists_hasCompactSupport_eLpNorm_sub_le
    ENNReal.one_ne_top (ENNReal.ofReal_ne_zero_iff.mpr hε')
  have hgi : Integrable g := memLp_one_iff_integrable.1 hg
  have hL1 : profileL1 (h - g) ≤ ε / 3 := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hh.sub hgi)] at hgap
    simpa only [profileL1, Real.norm_eq_abs] using (ENNReal.ofReal_le_ofReal_iff hε'.le).mp hgap
  have hL1' : profileL1 (g - h) ≤ ε / 3 := by
    simpa only [profileL1, Pi.sub_apply, abs_sub_comm (h _) (g _)] using hL1
  have hclose := (smoothProfile_L1_tendsto_of_continuous ρ g hρ hρnonneg hρmass hρsupport
    hgc hgk hs hδ hslim hδlim).eventually (Iio_mem_nhds hε')
  filter_upwards [hclose] with n hn
  let S := smoothProfile ρ (s n) (δ n)
  have hSi (f : FourierProfile) (hf : Integrable f) : Integrable (S f) :=
    integrable_convolve (dilateProfile_integrable hf (hs n))
      (dilateProfile_integrable (integrable_of_isProfile hρ) (hδ n))
  have ha := smoothProfile_contract ρ h g (integrable_of_isProfile hρ) hρnonneg hρmass hh hgi (hs n) (hδ n)
  have hb := profileL1_add_le ((hSi h hh).sub (hSi g hgi)) ((hSi g hgi).sub hgi)
  have hc := profileL1_add_le (((hSi h hh).sub (hSi g hgi)).add ((hSi g hgi).sub hgi)) (hgi.sub hh)
  have heq : (S h - S g) + (S g - g) + (g - h) = S h - h := by abel
  rw [heq] at hc
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (profileL1_nonneg _)]
  change profileL1 (S h - h) < ε
  change profileL1 (S g - g) < ε / 3 at hn
  linarith only [ha, hb, hc, hL1, hL1', hn]

end Chowla

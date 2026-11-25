import ZetaSixth.MomentWindows
import ZetaSixth.PairingProofs
import ZetaSixth.RegionGeometry
import Mathlib.LinearAlgebra.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

namespace ZetaSixth

open Filter MeasureTheory Set
open scoped Topology

private noncomputable def profileScore (V h : Profile) : ℝ :=
  2 * inner ℝ V h - ‖h‖ ^ 2

private theorem continuous_profileScore (V : Profile) : Continuous (profileScore V) := by
  unfold profileScore
  exact ((continuous_const.inner continuous_id).const_mul 2).sub (continuous_norm.pow 2)

/-- An element of the closed span gives a lower bound through the quadratic objective. -/
theorem bound_of_span_score {𝒯 : Family} (h𝒯 : Faithful 𝒯)
    (V : Profile) (hV : (V : Point → ℝ) =ᵐ[chamberVolume] v)
    {h : Profile} (hh : h ∈ familySpan 𝒯) {c : ℝ}
    (hc : c < (Nat.factorial 9 : ℝ) * (2 * inner ℝ V h - ‖h‖ ^ 2)) :
    ∀ᶠ T in atTop, c * c3 * T * Real.log T ^ 9 ≤ M6 T := by
  let span := Submodule.span ℝ (Prod.snd '' 𝒯)
  have hcl : h ∈ closure (span : Set Profile) := hh
  let O : Set Profile := {p | c < (Nat.factorial 9 : ℝ) * profileScore V p}
  have hO : IsOpen O := isOpen_lt continuous_const ((continuous_profileScore V).const_mul _)
  obtain ⟨w, hwO, hw⟩ := mem_closure_iff.1 hcl O hO hc
  let sndMap := LinearMap.snd ℝ Test Profile
  have hwmap : w ∈ (Submodule.span ℝ 𝒯).map sndMap := by
    rw [Submodule.map_span]
    exact hw
  obtain ⟨P, hP, hPw⟩ := Submodule.mem_map.1 hwmap
  change P.2 = w at hPw
  have hw' : c < (Nat.factorial 9 : ℝ) * (2 * inner ℝ V P.2 - ‖P.2‖ ^ 2) := by
    rw [hPw]
    exact hwO
  obtain ⟨d, hcd, hd⟩ := exists_between hw'
  exact sharp_of_smooth hcd (bound_of_profile_score h𝒯 V hV hP hd)

private theorem projection_inner {𝒯 : Family} (V : Profile) :
    inner ℝ V ((familySpan 𝒯).starProjection V) = ‖(familySpan 𝒯).starProjection V‖ ^ 2 := by
  have h := Submodule.starProjection_inner_eq_zero (K := familySpan 𝒯) V
    ((familySpan 𝒯).starProjection V) ((familySpan 𝒯).starProjection_apply_mem V)
  rw [inner_sub_left, real_inner_self_eq_norm_sq, sub_eq_zero] at h
  exact h

/-- Proposition 8 in eventual-bound form. -/
theorem projection_principle (𝒯 : Family) (h𝒯 : Faithful 𝒯)
    (V : Profile) (hV : (V : Point → ℝ) =ᵐ[chamberVolume] v)
    (c : ℝ) (hc : c < (Nat.factorial 9 : ℝ) * ‖(familySpan 𝒯).starProjection V‖ ^ 2) :
    ∀ᶠ T in atTop, c * c3 * T * Real.log T ^ 9 ≤ M6 T := by
  apply bound_of_span_score h𝒯 V hV ((familySpan 𝒯).starProjection_apply_mem V)
  rw [projection_inner (𝒯 := 𝒯) V, two_mul, add_sub_cancel_right]
  exact hc

private theorem omega_subset_box : Ω ⊆ Icc ((0, 0, 0) : Point) (1, 1, 1) := by
  intro p hp
  rcases hp with ⟨h₁, h₂, h₃, h₄⟩
  change (0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2) ∧
    (p.1 ≤ 1 ∧ p.2.1 ≤ 1 ∧ p.2.2 ≤ 1)
  exact ⟨⟨by linarith, by linarith, by linarith⟩, ⟨by linarith, by linarith, by linarith⟩⟩

private theorem memLp_v : MemLp v 2 chamberVolume := by
  have hcompact : IsCompact (Icc ((0, 0, 0) : Point) (1, 1, 1)) := isCompact_Icc
  letI : IsFiniteMeasure chamberVolume :=
    ⟨by
      rw [chamberVolume, Measure.restrict_apply_univ]
      exact (measure_mono omega_subset_box).trans_lt hcompact.measure_lt_top⟩
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn continuous_v.continuousOn
  apply MemLp.of_bound continuous_v.aestronglyMeasurable M
  filter_upwards [ae_restrict_mem (μ := (volume : Measure Point)) measurableSet_Ω] with p hp
  exact hM p (omega_subset_box hp)

/-- The L² class represented by the Weyl polynomial on the chamber. -/
noncomputable def targetProfile : Profile := memLp_v.toLp v

theorem targetProfile_ae : (targetProfile : Point → ℝ) =ᵐ[chamberVolume] v :=
  MemLp.coeFn_toLp memLp_v

private theorem indicator_inner (U : Set Point) (h : Profile)
    (hh : (h : Point → ℝ) =ᵐ[chamberVolume] U.indicator v) :
    inner ℝ targetProfile h = ‖h‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq h, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [targetProfile_ae, hh] with p hp hhp
  simp only [scalar_inner, hp, hhp]
  by_cases hpU : p ∈ U <;> simp [hpU]

/-- The real-valued mass equals the squared L² norm of the target restricted to the set. -/
theorem mu_toReal_eq_indicator (U : Set Point) (hU : MeasurableSet U) (h : Profile)
    (hh : (h : Point → ℝ) =ᵐ[chamberVolume] U.indicator v) :
    (μ U).toReal = (Nat.factorial 9 : ℝ) * ‖h‖ ^ 2 := by
  have hm : (∫ p in U, (Nat.factorial 9 : ℝ) * v p ^ 2 ∂chamberVolume) = (μ U).toReal := by
    rw [μ, withDensity_apply _ hU]
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => by positivity))
      ((continuous_const.mul (continuous_v.pow 2)).aestronglyMeasurable)
  rw [← hm, integral_const_mul, ← integral_indicator hU, ← real_inner_self_eq_norm_sq h,
    MeasureTheory.L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [hh] with p hp
  simp only [scalar_inner, hp]
  by_cases hpU : p ∈ U
  · simp [hpU, pow_two]
  · simp [hpU]

/-- The indicator case of Proposition 8 used for the mixed-row bound. -/
theorem bound_of_indicator (𝒯 : Family) (U : Set Point) (h𝒯 : Faithful 𝒯)
    (hU : MeasurableSet U) (_hSub : U ⊆ Ω) (hspan : InFamilySpan 𝒯 (U.indicator v))
    (c : ℝ) (hc : c < (μ U).toReal) :
    ∀ᶠ T in atTop, c * c3 * T * Real.log T ^ 9 ≤ M6 T := by
  obtain ⟨h, hh, hAE⟩ := hspan
  apply bound_of_span_score h𝒯 targetProfile targetProfile_ae hh
  rw [indicator_inner U h hAE, two_mul, add_sub_cancel_right, ← mu_toReal_eq_indicator U hU h hAE]
  exact hc

/-- The assembly uses the exact mass and the analytic hypothesis from the paper. -/
theorem main_of_mass (hmass : μ U7 = ENNReal.ofReal (C : ℝ))
    (h : PaperPairings) (c : ℝ) (hc : c < (C : ℝ)) :
    ∀ᶠ T in atTop, c * c3 * T * Real.log T ^ 9 ≤ M6 T := by
  obtain ⟨𝒯, h𝒯, hspan⟩ := h.exists_faithful
  have hC : 0 ≤ (C : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ C from (by norm_num : (0 : ℚ) ≤ 416406 / 10000).trans C_bounds.1.le)
  apply bound_of_indicator 𝒯 U7 h𝒯 measurableSet_U7 U7_subset_Ω hspan
  simpa only [hmass, ENNReal.toReal_ofReal hC] using hc

/-- Proposition 3 bounds the projection of the target for profiles supported on the ceiling. -/
theorem projection_ceiling (𝒯 : Family) (V : Profile)
    (hV : (V : Point → ℝ) =ᵐ[chamberVolume] v)
    (hSupp : ∀ (B : Test) (g : Profile), (B, g) ∈ 𝒯 →
      ∀ᵐ p ∂chamberVolume, p ∉ ceiling → g p = 0) :
    (Nat.factorial 9 : ℝ) * ‖(familySpan 𝒯).starProjection V‖ ^ 2 ≤ (μ ceiling).toReal := by
  let R := LpToLpRestrictCLM Point ℝ ℝ chamberVolume 2 ceilingᶜ
  have R_ae (g : Profile) : (R g : Point → ℝ) =ᵐ[chamberVolume.restrict ceilingᶜ] g :=
    LpToLpRestrictCLM_coeFn ℝ ceilingᶜ g
  have R_zero := Lp.coeFn_zero ℝ 2 (chamberVolume.restrict ceilingᶜ)
  have hspan : familySpan 𝒯 ≤ R.toLinearMap.ker := by
    apply Submodule.topologicalClosure_minimal _ _ R.isClosed_ker
    apply Submodule.span_le.2
    rintro g ⟨⟨B, h⟩, hBh, rfl⟩
    change R h = 0
    have hh : (h : Point → ℝ) =ᵐ[chamberVolume.restrict ceilingᶜ] 0 :=
      (ae_restrict_iff' measurableSet_ceiling.compl).2 (hSupp B h hBh)
    exact Lp.ext ((R_ae h).trans (hh.trans R_zero.symm))
  let p := (familySpan 𝒯).starProjection V
  have hp0 : R p = 0 := hspan ((familySpan 𝒯).starProjection_apply_mem V)
  have hp_ae : ∀ᵐ x ∂chamberVolume, x ∉ ceiling → p x = 0 := by
    apply (ae_restrict_iff' measurableSet_ceiling.compl).1
    have h := (R_ae p).symm
    rw [hp0] at h
    exact h.trans R_zero
  let hv : MemLp (ceiling.indicator v) 2 chamberVolume :=
    MemLp.indicator measurableSet_ceiling memLp_v
  let W : Profile := hv.toLp _
  have hW : (W : Point → ℝ) =ᵐ[chamberVolume] ceiling.indicator v := MemLp.coeFn_toLp hv
  have hi : inner ℝ V p = inner ℝ W p := by
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hV, hW, hp_ae] with x hx hxW hxp
    by_cases hxc : x ∈ ceiling
    · simp [hx, hxW, hxc]
    · simp [hxp hxc]
  have hnorm : ‖p‖ ≤ ‖W‖ := by
    have hb : ‖p‖ ^ 2 ≤ ‖W‖ * ‖p‖ := by
      rw [← projection_inner (𝒯 := 𝒯) V, hi]
      exact real_inner_le_norm _ _
    by_cases hp : ‖p‖ = 0
    · simp [hp]
    · have hp_pos : 0 < ‖p‖ := lt_of_le_of_ne (norm_nonneg p) (Ne.symm hp)
      apply (mul_le_mul_iff_left₀ hp_pos).1
      simpa only [pow_two] using hb
  rw [mu_toReal_eq_indicator ceiling measurableSet_ceiling W hW]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg p) hnorm 2) (by positivity)

end ZetaSixth

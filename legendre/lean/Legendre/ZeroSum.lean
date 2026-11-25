import Legendre.ZetaReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

namespace Legendre

open Complex Filter MeasureTheory Set
open scoped BigOperators Interval Topology

private theorem zeroCount_mono : Monotone zeroCount := by
  classical
  intro s t hst
  unfold zeroCount
  apply Finset.sum_le_sum_of_subset
  simp only [Finset.subset_iff, Finset.mem_filter, mem_zerosIn]
  intro ρ hρ
  exact ⟨⟨hρ.1.1, hρ.1.2.1, hρ.1.2.2.trans hst⟩, hρ.2⟩

private theorem zeroCountMain_lower (t : ℝ) (ht : 0 < t) : -(1 / 8 : ℝ) ≤ zeroCountMain t := by
  have hπ : 0 < 2 * Real.pi := by positivity
  let s := t / (2 * Real.pi)
  have hs : 0 < s := div_pos ht hπ
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hs)
  rw [Real.log_inv] at h
  have hh := mul_le_mul_of_nonneg_right h hs.le
  have hcancel : s⁻¹ * s = 1 := inv_mul_cancel₀ hs.ne'
  rw [sub_mul, hcancel, one_mul] at hh
  have hlog : Real.log (t / (2 * Real.pi * Real.exp 1)) = Real.log s - 1 := by
    rw [← div_div, Real.log_div hs.ne' (Real.exp_pos 1).ne', Real.log_exp]
  rw [zeroCountMain, hlog]
  change -(1 / 8 : ℝ) ≤ s * (Real.log s - 1) + 7 / 8
  linarith only [hh, show s * (Real.log s - 1) = Real.log s * s - s by ring]

private theorem zeroCount_exp_one_le_two (h : CitedFacts) : zeroCount (Real.exp 1) ≤ 2 := by
  have hπ₁ : 3 < Real.pi := by linarith [Real.pi_gt_d2]
  have hπ₂ : Real.pi < 3.2 := by linarith [Real.pi_lt_d2]
  have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact Real.exp_one_lt_three
  have hlog6 : (1.5 : ℝ) < Real.log 6 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_gt_d9]
  have hlogπ : (1.5 : ℝ) < Real.log (2 * Real.pi) :=
    hlog6.trans (Real.log_lt_log (by norm_num) (by linarith))
  have hr : (0.42 : ℝ) < Real.exp 1 / (2 * Real.pi) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hratio : Real.exp 1 / (2 * Real.pi * Real.exp 1) = (2 * Real.pi)⁻¹ := by
    field_simp
  have hmain : zeroCountMain (Real.exp 1) < 0.25 := by
    rw [zeroCountMain, hratio, Real.log_inv]
    nlinarith only [mul_pos (sub_pos.mpr hr) (sub_pos.mpr hlogπ), hr, hlogπ]
  have ht := h.trudgian (Real.exp 1) le_rfl
  rw [Real.log_exp, Real.log_one, mul_zero, add_zero] at ht
  have hupper : (zeroCount (Real.exp 1) : ℝ) - zeroCountMain (Real.exp 1) ≤
      0.112 * 1 + 2.510 + 0.2 / Real.exp 1 := by
    simpa only [zeroCountMain, sub_add_eq_sub_sub] using (abs_le.mp ht).2
  have hdiv : 0.2 / Real.exp 1 < (0.1 : ℝ) := by
    rw [div_lt_iff₀ (Real.exp_pos 1)]
    linarith
  have hlt : (zeroCount (Real.exp 1) : ℝ) < 3 := by linarith
  have hn : zeroCount (Real.exp 1) < 3 := by exact_mod_cast hlt
  omega

/-- Lemma 15, obtained from Trudgian's estimate at and above `e` and monotonicity below it. -/
theorem zeroCount_error (h : CitedFacts) (t : ℝ) (ht : 0 < t) :
    |(zeroCount t : ℝ) - zeroCountMain t| ≤ 3 + 0.15 * logPlus t := by
  by_cases he : Real.exp 1 ≤ t
  · have hlog : 1 ≤ Real.log t := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) he
    have hlogPos : 0 < Real.log t := by linarith
    have htangent := Real.log_le_sub_one_of_pos (show 0 < Real.log t / 8 by positivity)
    rw [Real.log_div hlogPos.ne' (by norm_num)] at htangent
    have h8 : Real.log 8 < 2.1 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      linarith [Real.log_two_lt_d9]
    have hdiv : 0.2 / t < (0.1 : ℝ) := by
      rw [div_lt_iff₀ ht]
      linarith [Real.exp_one_gt_two]
    rw [logPlus, max_eq_left hlogPos.le]
    have hTr : |(zeroCount t : ℝ) - zeroCountMain t| ≤
        0.112 * Real.log t + 0.278 * Real.log (Real.log t) + 2.510 + 0.2 / t := by
      simpa only [zeroCountMain, sub_add_eq_sub_sub] using h.trudgian t he
    exact hTr.trans (by linarith)
  · have hπ : 1 < 2 * Real.pi := by linarith [Real.pi_gt_d2]
    have hu : t / (2 * Real.pi * Real.exp 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact (le_of_not_ge he).trans (le_mul_of_one_le_left (Real.exp_pos 1).le hπ.le)
    have hprod : t / (2 * Real.pi) * Real.log (t / (2 * Real.pi * Real.exp 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (Real.log_nonpos (by positivity) hu)
    have hhi : zeroCountMain t ≤ 7 / 8 := by rw [zeroCountMain]; linarith
    have hlo := zeroCountMain_lower t ht
    have hN : (zeroCount t : ℝ) ≤ 2 := by
      exact_mod_cast (zeroCount_mono (le_of_not_ge he)).trans (zeroCount_exp_one_le_two h)
    have hN₀ : (0 : ℝ) ≤ zeroCount t := by positivity
    have hplus : 0 ≤ logPlus t := le_max_right _ _
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The distinct nontrivial zeros with ordinate in `(0,t]`. -/
noncomputable def positiveZeros (t : ℝ) : Finset ℂ := by
  classical
  exact (zerosIn 0 t).filter (fun ρ ↦ 0 < ρ.im)

@[simp] theorem mem_positiveZeros {t : ℝ} {ρ : ℂ} :
    ρ ∈ positiveZeros t ↔ ρ ∈ nontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ t := by
  classical
  simp only [positiveZeros, Finset.mem_filter, mem_zerosIn]
  constructor
  · rintro ⟨⟨hρ, _, hT⟩, h₀⟩
    exact ⟨hρ, h₀, hT⟩
  · rintro ⟨hρ, h₀, hT⟩
    exact ⟨⟨hρ, h₀.le, hT⟩, h₀⟩

private theorem positiveZeros_filter {T t : ℝ} (ht : t ≤ T) :
    ((positiveZeros T).filter fun ρ ↦ ρ.im ≤ t) = positiveZeros t := by
  classical
  ext ρ
  simp only [Finset.mem_filter, mem_positiveZeros]
  constructor
  · rintro ⟨⟨hρ, h₀, _⟩, h₁⟩
    exact ⟨hρ, h₀, h₁⟩
  · rintro ⟨hρ, h₀, h₁⟩
    exact ⟨⟨hρ, h₀, h₁.trans ht⟩, h₁⟩

private theorem cast_zeroCount (t : ℝ) :
    (zeroCount t : ℝ) = ∑ ρ ∈ positiveZeros t, (zeroMultiplicity ρ : ℝ) := by
  rw [← Nat.cast_sum]
  rfl

/-- Finite summation by parts for zeros with positive ordinate. -/
theorem finite_zero_summation_by_parts (φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hφ : AbsolutelyContinuousOnInterval φ 0 T) :
    (∑ ρ ∈ positiveZeros T, (zeroMultiplicity ρ : ℝ) * φ ρ.im) =
      (zeroCount T : ℝ) * φ T - ∫ t in 0..T, (zeroCount t : ℝ) * deriv φ t := by
  classical
  let f (ρ : ℂ) : ℝ → ℝ := (Ici ρ.im).indicator (fun t ↦ (zeroMultiplicity ρ : ℝ) * deriv φ t)
  have hint (ρ : ℂ) : IntervalIntegrable (f ρ) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact ((hφ.intervalIntegrable_deriv.1).const_mul _).indicator measurableSet_Ici
  have hsum : (∫ t in 0..T, (zeroCount t : ℝ) * deriv φ t) =
      ∑ ρ ∈ positiveZeros T, ∫ t in 0..T, f ρ t := by
    rw [← intervalIntegral.integral_finset_sum (fun ρ _ ↦ hint ρ)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT] at ht
    dsimp only
    rw [cast_zeroCount, ← positiveZeros_filter ht.2, Finset.sum_mul, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun _ _ ↦ rfl)
  have hterm (ρ : ℂ) (hρ : ρ ∈ positiveZeros T) :
      (∫ t in 0..T, f ρ t) = (zeroMultiplicity ρ : ℝ) * (φ T - φ ρ.im) := by
    obtain ⟨_, hl, hu⟩ := mem_positiveZeros.mp hρ
    have hsub : uIcc ρ.im T ⊆ uIcc 0 T := by
      rw [uIcc_of_le hu, uIcc_of_le hT]
      exact Icc_subset_Icc_left hl.le
    have heq : Ioc 0 T ∩ Ici ρ.im = Icc ρ.im T := by
      ext t
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨hl.trans_le h.1, h.2⟩, h.1⟩⟩
    change (∫ t in 0..T, (Ici ρ.im).indicator (fun t ↦ (zeroMultiplicity ρ : ℝ) * deriv φ t) t) = _
    rw [intervalIntegral.integral_of_le hT, setIntegral_indicator measurableSet_Ici, heq,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu,
      intervalIntegral.integral_const_mul, (hφ.mono hsub).integral_deriv_eq_sub]
  rw [hsum, Finset.sum_congr rfl hterm, cast_zeroCount, Finset.sum_mul, ← Finset.sum_sub_distrib]
  congr 1 with ρ
  ring

private theorem mainTerm_eq (t : ℝ) : zeroCountMain t =
    t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8 := by
  by_cases ht : t = 0
  · simp [ht, zeroCountMain]
  have hπ : 2 * Real.pi ≠ 0 := by positivity
  unfold zeroCountMain
  rw [← div_div t (2 * Real.pi) (Real.exp 1), Real.log_div (div_ne_zero ht hπ)
    (Real.exp_pos 1).ne', Real.log_exp]
  ring

private noncomputable def mainDensity (t : ℝ) : ℝ := Real.log (t / (2 * Real.pi)) / (2 * Real.pi)

private theorem mainTerm_continuous : Continuous zeroCountMain := by
  change Continuous (fun t ↦ zeroCountMain t)
  simp_rw [mainTerm_eq]
  exact ((Real.continuous_mul_log.comp (continuous_id.div_const _)).sub
    (continuous_id.div_const _)).add continuous_const

private theorem mainTerm_hasDerivAt {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt zeroCountMain (mainDensity t) t := by
  let den := 2 * Real.pi
  have hp : 0 < den := by dsimp [den]; positivity
  have h' := (Real.hasDerivAt_mul_log (div_ne_zero ht hp.ne')).comp t
    ((hasDerivAt_id t).div_const den)
  have h'' := (h'.sub ((hasDerivAt_id t).div_const den)).add_const (7 / 8)
  convert h'' using 1
  · funext x
    simp [mainTerm_eq, Function.comp_def, den]
  · dsimp [mainDensity, den]
    ring

private theorem mainDensity_intervalIntegrable (T : ℝ) :
    IntervalIntegrable mainDensity volume 0 T := by
  have hπ : 2 * Real.pi ≠ 0 := by positivity
  have hlog : IntervalIntegrable Real.log volume 0 T := intervalIntegral.intervalIntegrable_log'
  have hint := (hlog.sub (intervalIntegrable_const (c := Real.log (2 * Real.pi)))).div_const
    (2 * Real.pi)
  apply hint.congr_ae
  have he : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (0 : ℝ) :=
    compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  filter_upwards [he.filter_mono (ae_mono Measure.restrict_le_self)] with x hx
  simp [mainDensity, Real.log_div hx hπ]

private theorem integral_mainDensity (t : ℝ) :
    (∫ y in 0..t, mainDensity y) = zeroCountMain t - zeroCountMain 0 := by
  by_cases ht : 0 ≤ t
  · exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht mainTerm_continuous.continuousOn
      (fun x hx ↦ mainTerm_hasDerivAt hx.1.ne') (mainDensity_intervalIntegrable t)
  · rw [intervalIntegral.integral_symm]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_not_ge ht)
      mainTerm_continuous.continuousOn (fun x hx ↦ mainTerm_hasDerivAt hx.2.ne)
      (mainDensity_intervalIntegrable t).symm]
    ring

private theorem mainTerm_absContinuous (T : ℝ) :
    AbsolutelyContinuousOnInterval zeroCountMain 0 T := by
  have hc : AbsolutelyContinuousOnInterval (fun _ ↦ zeroCountMain 0) 0 T := by
    rw [absolutelyContinuousOnInterval_iff]
    intro ε hε
    exact ⟨1, zero_lt_one, fun _ _ _ ↦ by simpa using hε⟩
  have hAC := ((mainDensity_intervalIntegrable T).absolutelyContinuousOnInterval_intervalIntegral
    (c := 0) (by simp)).fun_add hc
  exact (show (fun t ↦ (∫ y in 0..t, mainDensity y) + zeroCountMain 0) = zeroCountMain from by
    funext t
    rw [integral_mainDensity, sub_add_cancel]) ▸ hAC

private theorem zeroCount_zero : zeroCount 0 = 0 := by
  have he : positiveZeros 0 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ρ hρ
    have := mem_positiveZeros.mp hρ
    linarith only [this.2.1, this.2.2]
  change (∑ ρ ∈ positiveZeros 0, zeroMultiplicity ρ) = 0
  rw [he, Finset.sum_empty]

private noncomputable def countError (t : ℝ) : ℝ := (zeroCount t : ℝ) - zeroCountMain t

private theorem measurable_countError : Measurable countError := by
  have hm : Monotone (fun t : ℝ ↦ (zeroCount t : ℝ)) := by
    intro s t hst
    exact Nat.cast_le.mpr (zeroCount_mono hst)
  exact hm.measurable.sub mainTerm_continuous.measurable

private theorem countError_intervalIntegrable (φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hφ : AbsolutelyContinuousOnInterval φ 0 T) :
    IntervalIntegrable (fun t ↦ countError t * deriv φ t) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn mainTerm_continuous.continuousOn
    (s := Icc (0 : ℝ) T)
  have hδ := (hφ.intervalIntegrable_deriv.1.norm.const_mul ((zeroCount T : ℝ) + B))
  refine hδ.mono' (measurable_countError.aestronglyMeasurable.mul
    hφ.intervalIntegrable_deriv.1.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := T))] with x hx
  have h₁ : (zeroCount x : ℝ) ≤ zeroCount T := by exact_mod_cast zeroCount_mono hx.2
  have h₂ : ‖(zeroCount x : ℝ)‖ = zeroCount x := Real.norm_of_nonneg (Nat.cast_nonneg _)
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  unfold countError
  exact (norm_sub_le _ _).trans (add_le_add (h₂.trans_le h₁) (hB x ⟨hx.1.le, hx.2⟩))

private theorem countError_summation_by_parts (φ : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hφ : AbsolutelyContinuousOnInterval φ 0 T) :
    (∑ ρ ∈ positiveZeros T, (zeroMultiplicity ρ : ℝ) * φ ρ.im) =
      countError T * φ T + (7 / 8 : ℝ) * φ 0 + (∫ t in 0..T, mainDensity t * φ t) -
      ∫ t in 0..T, countError t * deriv φ t := by
  have hM := mainTerm_absContinuous T
  have hParts := hM.integral_mul_deriv_eq_deriv_mul hφ
  have hdiv : (∫ t in 0..T, deriv zeroCountMain t * φ t) = ∫ t in 0..T, mainDensity t * φ t := by
    apply intervalIntegral.integral_congr_ae
    rw [uIoc_of_le hT]
    exact Eventually.of_forall (fun t (ht : t ∈ Ioc (0 : ℝ) T) ↦ by
      rw [(mainTerm_hasDerivAt ht.1.ne').deriv])
  have hintegM : IntervalIntegrable (fun t ↦ zeroCountMain t * deriv φ t) volume 0 T :=
    hφ.intervalIntegrable_deriv.continuousOn_mul mainTerm_continuous.continuousOn
  have hsplit : (∫ t in 0..T, (zeroCount t : ℝ) * deriv φ t) =
      (∫ t in 0..T, zeroCountMain t * deriv φ t) + ∫ t in 0..T, countError t * deriv φ t := by
    rw [← intervalIntegral.integral_add hintegM (countError_intervalIntegrable φ hT hφ)]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [countError]
    ring
  rw [finite_zero_summation_by_parts φ hT hφ, hsplit, hParts, hdiv]
  have he : zeroCountMain 0 = 7 / 8 := by simp [zeroCountMain]
  rw [he]
  simp only [countError]
  ring

private theorem absScaled_absContinuous {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (δ T : ℝ) :
    AbsolutelyContinuousOnInterval (fun t ↦ |F (δ * t)|) 0 T := by
  have hc : ContDiff ℝ 1 (fun t : ℝ ↦ F (δ * t)) := hF.comp (by fun_prop)
  obtain ⟨K, hK⟩ := hc.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_uIcc 0 T) isCompact_uIcc
  have habs : LipschitzWith 1 (abs : ℝ → ℝ) := LipschitzWith.of_dist_le_mul fun a b ↦ by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using norm_abs_sub_abs a b
  exact (habs.comp_lipschitzOnWith hK).absolutelyContinuousOnInterval

private theorem abs_deriv_absScaled_le {F : ℝ → ℝ} (hF : Differentiable ℝ F) {δ : ℝ}
    (hδ : 0 ≤ δ) (t : ℝ) :
    |deriv (fun x : ℝ ↦ |F (δ * x)|) t| ≤ δ * |deriv F (δ * t)| := by
  have hd := (hF (δ * t)).hasDerivAt.comp t ((hasDerivAt_id t).const_mul δ)
  by_cases h : F (δ * t) = 0
  · have hlocal : IsLocalMin (fun x : ℝ ↦ |F (δ * x)|) t :=
      IsMinOn.isLocalMin (s := univ) (fun x _ ↦ by simp [h])
        (by simp)
    rw [hlocal.deriv_eq_zero, abs_zero]
    positivity
  · rcases lt_or_gt_of_ne h with hn | hp
    · have ht := (hasDerivAt_abs_neg hn).comp t hd
      change HasDerivAt (fun x : ℝ ↦ |F (δ * x)|) (-1 * (deriv F (δ * t) * (δ * 1))) t at ht
      rw [ht.deriv]
      simp [abs_mul, abs_of_nonneg hδ, mul_comm]
    · have ht := (hasDerivAt_abs_pos hp).comp t hd
      change HasDerivAt (fun x : ℝ ↦ |F (δ * x)|) (1 * (deriv F (δ * t) * (δ * 1))) t at ht
      rw [ht.deriv]
      simp [abs_mul, abs_of_nonneg hδ, mul_comm]

private theorem abs_fourier_decay_on_Ioi {F : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ y : ℝ, |F y| ≤ C / (1 + |y|) ^ 2) {y : ℝ} (hy : 0 < y) :
    |F y| ≤ C * y ^ (-2 : ℝ) := by
  refine (hdecay y).trans ?_
  rw [abs_of_pos hy, Real.rpow_neg hy.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  rw [← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left hC (sq_pos_of_pos hy)
    (pow_le_pow_left₀ hy.le (by linarith) 2)

private theorem fourier_integrableOn_Ioi {F : ℝ → ℝ} (hF : Continuous F) {C : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ y : ℝ, |F y| ≤ C / (1 + |y|) ^ 2) :
    IntegrableOn (fun y ↦ |F y|) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  refine ⟨(hF.abs.continuousOn.integrableOn_Icc (a := (0 : ℝ)) (b := 1)).mono_set Ioc_subset_Icc_self, ?_⟩
  refine ((integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) zero_lt_one).const_mul C).mono'
    hF.abs.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (1 : ℝ)))] with y hy
  simpa only [Real.norm_eq_abs, abs_abs] using abs_fourier_decay_on_Ioi hC hdecay (zero_lt_one.trans hy)

private theorem log_moment_integrableOn_Ioi {F : ℝ → ℝ} (hF : Continuous F) {C M : ℝ}
    (hC : 0 ≤ C) (hdecay : ∀ y : ℝ, |F y| ≤ C / (1 + |y|) ^ 2) (hM : ∀ y, |F y| ≤ M) :
    IntegrableOn (fun y ↦ |F y| * Real.log y) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  have hmeas : Measurable (fun y ↦ |F y| * Real.log y) := hF.abs.measurable.mul Real.measurable_log
  constructor
  · have hlog : IntervalIntegrable Real.log volume 0 1 := intervalIntegral.intervalIntegrable_log'
    refine (hlog.1.norm.const_mul M).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun y ↦ ?_)
    rw [norm_mul, Real.norm_eq_abs, abs_abs]
    exact mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)
  · refine ((integrableOn_Ioi_rpow_of_lt (show (-3 / 2 : ℝ) < -1 by norm_num) zero_lt_one).const_mul
      (2 * C)).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (1 : ℝ)))] with y hy
    have hy₀ : 0 < y := (zero_lt_one : (0 : ℝ) < 1).trans hy
    have hlog := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy₀ (1 / 2 : ℝ))
    rw [Real.log_rpow hy₀] at hlog
    have hlog' : Real.log y ≤ 2 * y ^ (1 / 2 : ℝ) := by linarith
    have hlog₀ : 0 ≤ Real.log y := Real.log_nonneg hy.le
    rw [norm_mul, Real.norm_eq_abs, abs_abs, Real.norm_of_nonneg hlog₀]
    calc
      _ ≤ (C * y ^ (-2 : ℝ)) * (2 * y ^ (1 / 2 : ℝ)) :=
        mul_le_mul (abs_fourier_decay_on_Ioi hC hdecay hy₀) hlog' hlog₀ (by positivity)
      _ = _ := by
        rw [show C * y ^ (-2 : ℝ) * (2 * y ^ (1 / 2 : ℝ)) =
          (2 * C) * (y ^ (-2 : ℝ) * y ^ (1 / 2 : ℝ)) by ring, ← Real.rpow_add hy₀]
        norm_num

private theorem logPlus_scale_le {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) :
    logPlus t ≤ logPlus δ⁻¹ + logPlus (δ * t) := by
  unfold logPlus
  apply max_le
  · rw [Real.log_mul hδ.ne' ht.ne', Real.log_inv]
    linarith only [le_max_left (Real.log δ + Real.log t) 0, le_max_left (-Real.log δ) 0]
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

private noncomputable def variationMajorant (F : ℝ → ℝ) (δ y : ℝ) : ℝ :=
  (3 + 0.15 * logPlus δ⁻¹) * |deriv F y| + 0.15 * (logPlus y * |deriv F y|)

private theorem integral_error_bound (h : CitedFacts) {F : ℝ → ℝ} (hF : Differentiable ℝ F)
    (hV₀ : IntegrableOn (fun y ↦ |deriv F y|) (Ioi 0))
    (hV₁ : IntegrableOn (fun y ↦ logPlus y * |deriv F y|) (Ioi 0))
    {δ : ℝ} (hδ : 0 < δ) :
    let f : ℝ → ℝ := fun t ↦ countError t * deriv (fun x : ℝ ↦ |F (δ * x)|) t
    IntegrableOn f (Ioi 0) ∧ |∫ t in Ioi (0 : ℝ), f t| ≤
      (3 + 0.15 * logPlus δ⁻¹) * totalVariation F + 0.15 * logVariation F := by
  let f : ℝ → ℝ := fun t ↦ countError t * deriv (fun x : ℝ ↦ |F (δ * x)|) t
  have hW : IntegrableOn (variationMajorant F δ) (Ioi 0) :=
    (hV₀.const_mul _).add (hV₁.const_mul _)
  have hWC : IntegrableOn (fun t ↦ δ * variationMajorant F δ (δ * t)) (Ioi 0) := by
    have hscale := (integrableOn_Ioi_comp_mul_left_iff (variationMajorant F δ) 0 hδ).mpr
      (by simpa only [mul_zero] using hW)
    exact hscale.const_mul _
  have hmeas : Measurable f := measurable_countError.mul (measurable_deriv _)
  have hbd : ∀ t ∈ Ioi (0 : ℝ), ‖f t‖ ≤ δ * variationMajorant F δ (δ * t) := by
    intro t ht
    have htp : 0 < t := ht
    have hR := zeroCount_error h t htp
    change |countError t| ≤ _ at hR
    have hφ' := abs_deriv_absScaled_le hF hδ.le t
    have hL := logPlus_scale_le hδ htp
    have hR' : |countError t| ≤ 3 + 0.15 * (logPlus δ⁻¹ + logPlus (δ * t)) := by linarith
    have hC : 0 ≤ 3 + 0.15 * (logPlus δ⁻¹ + logPlus (δ * t)) := (abs_nonneg _).trans hR'
    dsimp only [f]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      _ ≤ (3 + 0.15 * (logPlus δ⁻¹ + logPlus (δ * t))) *
          (δ * |deriv F (δ * t)|) := mul_le_mul hR' hφ' (abs_nonneg _) hC
      _ = _ := by unfold variationMajorant; ring
  have hi : IntegrableOn f (Ioi 0) := hWC.mono' hmeas.aestronglyMeasurable (by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    exact hbd t ht)
  refine ⟨hi, ?_⟩
  rw [← Real.norm_eq_abs]
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), δ * variationMajorant F δ (δ * t) :=
      setIntegral_mono_on hi.norm hWC measurableSet_Ioi hbd
    _ = ∫ y in Ioi (0 : ℝ), variationMajorant F δ y := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi _ _ hδ, mul_zero, smul_eq_mul,
        ← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul]
    _ = _ := by
      unfold variationMajorant totalVariation logVariation
      rw [integral_add (hV₀.const_mul _) (hV₁.const_mul _), integral_const_mul, integral_const_mul]

private theorem tendsto_countError_absScaled (h : CitedFacts) {F : ℝ → ℝ} {δ C : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hdecay : ∀ y, |F y| ≤ C / (1 + |y|) ^ 2) :
    Tendsto (fun t : ℝ ↦ countError t * |F (δ * t)|) atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ ↦ (4 * C / δ ^ 2) * t⁻¹) atTop (𝓝 0) := by
    simpa only [Pi.inv_apply, mul_zero] using
      (tendsto_id (α := ℝ)).inv_tendsto_atTop.const_mul (4 * C / δ ^ 2)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht₀ : 0 < t := zero_lt_one.trans_le ht
  have hR := zeroCount_error h t ht₀
  change |countError t| ≤ _ at hR
  have hlog : logPlus t ≤ t := by
    exact max_le ((Real.log_le_sub_one_of_pos ht₀).trans (by linarith)) ht₀.le
  have hR' : |countError t| ≤ 4 * t := by
    linarith only [hR, hlog, ht]
  have hF : |F (δ * t)| ≤ C / (δ * t) ^ 2 := by
    simpa only [Real.rpow_neg (mul_nonneg hδ.le ht₀.le), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, div_eq_mul_inv] using
        abs_fourier_decay_on_Ioi hC hdecay (mul_pos hδ ht₀)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
  calc
    _ ≤ 4 * t * (C / (δ * t) ^ 2) :=
      mul_le_mul hR' hF (abs_nonneg _) (by positivity)
    _ = _ := by field_simp [hδ.ne', ht₀.ne']

private theorem even_integral_eq {g : ℝ → ℝ} (hg : Function.Even g) :
    (∫ y, g y) = 2 * ∫ y in Ioi (0 : ℝ), g y := by
  calc
    (∫ y, g y) = ∫ y, g |y| := by
      apply integral_congr_ae
      filter_upwards with y
      rcases le_or_gt 0 y with hy | hy
      · simp only [abs_of_nonneg hy]
      · rw [abs_of_neg hy, hg y]
    _ = _ := integral_comp_abs

private theorem integral_main_density_scaled {F : ℝ → ℝ} (heven : Function.Even F)
    (hF : IntegrableOn (fun y ↦ |F y|) (Ioi 0))
    (hL : IntegrableOn (fun y ↦ |F y| * Real.log y) (Ioi 0))
    {D : ℝ} (hD : 0 < D) :
    let δ := D / (2 * Real.pi)
    let f : ℝ → ℝ := fun t ↦ mainDensity t * |F (δ * t)|
    IntegrableOn f (Ioi 0) ∧ 2 * D * (∫ t in Ioi (0 : ℝ), f t) =
      fourierMass F * Real.log (1 / D) + logMoment F := by
  let c := 2 * Real.pi
  let δ := D / c
  let f : ℝ → ℝ := fun t ↦ mainDensity t * |F (δ * t)|
  have hc : 0 < c := by dsimp [c]; positivity
  have hδ : 0 < δ := div_pos hD hc
  let g : ℝ → ℝ := fun y ↦ (|F y| * Real.log (1 / D) + (|F y| * Real.log y)) / c
  have hg : IntegrableOn g (Ioi 0) := ((hF.mul_const _).add hL).div_const _
  have hEq : ∀ t ∈ Ioi (0 : ℝ), f t = g (δ * t) := by
    intro t ht
    have ht₀ : 0 < t := ht
    have hdt : 0 < δ * t := mul_pos hδ ht₀
    have harith : t / c = (δ * t) / D := by dsimp only [δ]; field_simp
    change Real.log (t / c) / c * |F (δ * t)| = _
    dsimp only [g]
    rw [harith, Real.log_div hdt.ne' hD.ne', Real.log_div one_ne_zero hD.ne', Real.log_one]
    ring
  have hi : IntegrableOn f (Ioi 0) := by
    have hg' := (integrableOn_Ioi_comp_mul_left_iff g 0 hδ).mpr (by simpa only [mul_zero] using hg)
    exact hg'.congr_fun (fun t ht ↦ (hEq t ht).symm) measurableSet_Ioi
  refine ⟨hi, ?_⟩
  change 2 * D * (∫ t in Ioi (0 : ℝ), f t) = _
  rw [setIntegral_congr_fun measurableSet_Ioi hEq, integral_comp_mul_left_Ioi _ _ hδ, mul_zero,
    smul_eq_mul]
  have he1 : Function.Even (fun y ↦ |F y|) := fun y ↦ by
    dsimp only
    rw [heven y]
  have he2 : Function.Even (fun y ↦ |F y| * Real.log |y|) := fun y ↦ by
    dsimp only
    rw [heven y, abs_neg]
  have hm : (∫ y in Ioi (0 : ℝ), |F y| * Real.log |y|) =
      ∫ y in Ioi (0 : ℝ), |F y| * Real.log y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    simp only [abs_of_pos (show 0 < y from hy)]
  unfold fourierMass logMoment g
  rw [even_integral_eq he1, even_integral_eq he2, hm, integral_div,
    integral_add (hF.mul_const _) hL, integral_mul_const]
  dsimp only [δ]
  field_simp [hD.ne', hc.ne']

private noncomputable def positiveWeight (φ : ℝ → ℝ) (ρ : nontrivialZeros) : ℝ := by
  classical
  exact if 0 < (ρ : ℂ).im then (zeroMultiplicity ρ : ℝ) * φ (ρ : ℂ).im else 0

private theorem positiveWeight_finset_le (φ : ℝ → ℝ) (hφ : ∀ t, 0 ≤ φ t)
    (u : Finset nontrivialZeros) {T : ℝ} (hu : ∀ ρ ∈ u, (ρ : ℂ).im ≤ T) :
    ∑ ρ ∈ u, positiveWeight φ ρ ≤ ∑ ρ ∈ positiveZeros T, (zeroMultiplicity ρ : ℝ) * φ ρ.im := by
  classical
  let S := (positiveZeros T).subtype (fun ρ ↦ ρ ∈ nontrivialZeros)
  have hsub : u.filter (fun ρ : nontrivialZeros ↦ 0 < (ρ : ℂ).im) ⊆ S := by
    intro ρ hρ
    rcases Finset.mem_filter.mp hρ with ⟨huρ, hp⟩
    exact Finset.mem_subtype.mpr (mem_positiveZeros.mpr ⟨ρ.property, hp, hu ρ huρ⟩)
  calc
    _ = ∑ ρ ∈ u.filter (fun ρ : nontrivialZeros ↦ 0 < (ρ : ℂ).im),
        (zeroMultiplicity ρ : ℝ) * φ (ρ : ℂ).im := by
      rw [Finset.sum_filter]
      rfl
    _ ≤ ∑ ρ ∈ S, (zeroMultiplicity ρ : ℝ) * φ (ρ : ℂ).im :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ _ _ ↦
        mul_nonneg (Nat.cast_nonneg _) (hφ (ρ : ℂ).im))
    _ = _ := by
      let weight (ρ : ℂ) : ℝ := (zeroMultiplicity ρ : ℝ) * φ ρ.im
      change (∑ ρ ∈ (positiveZeros T).subtype (fun ρ ↦ ρ ∈ nontrivialZeros), weight ρ) =
        ∑ ρ ∈ positiveZeros T, weight ρ
      have he : (positiveZeros T).filter (fun ρ ↦ ρ ∈ nontrivialZeros) = positiveZeros T :=
        Finset.filter_true_of_mem fun _ hρ ↦ (mem_positiveZeros.mp hρ).1
      rw [Finset.sum_subtype_eq_sum_filter weight, he]

private theorem zeroWeight_eq_pos_pair (hRH : RiemannHypothesis) {F : ℝ → ℝ}
    (heven : Function.Even F) (D : ℝ) (ρ : nontrivialZeros) :
    let φ := fun t ↦ |F (D / (2 * Real.pi) * t)|
    weightedZeroNorm F D ρ = positiveWeight φ ρ + positiveWeight φ (reflectZero ρ) := by
  classical
  let φ := fun t ↦ |F (D / (2 * Real.pi) * t)|
  have hφ : Function.Even φ := fun t ↦ by
    simp only [φ, mul_neg, heven (D / (2 * Real.pi) * t)]
  have him : ((reflectZero ρ : nontrivialZeros) : ℂ).im = -(ρ : ℂ).im := by
    change (1 - (ρ : ℂ)).im = _
    simp
  have hm : zeroMultiplicity (reflectZero ρ) = zeroMultiplicity ρ :=
    zeroMultiplicity_reflect ρ.property
  change (zeroMultiplicity ρ : ℝ) * φ (ρ : ℂ).im =
    positiveWeight φ ρ + positiveWeight φ (reflectZero ρ)
  unfold positiveWeight
  simp only [him, hm, hφ (ρ : ℂ).im, neg_pos]
  rcases lt_or_gt_of_ne (nontrivialZero_im_ne_zero_of_RH hRH ρ.property) with hn | hp
  · simp only [not_lt_of_ge hn.le, if_false, hn, if_true, zero_add]
  · simp only [not_lt_of_ge hp.le, if_false, hp, if_true, add_zero]

private theorem zero_sum_bound_logPlus (hRH : RiemannHypothesis) (h : CitedFacts) (F : ℝ → ℝ)
    (heven : Function.Even F) (hC : ContDiff ℝ 1 F)
    (hdecay : ∃ C : ℝ, ∀ y : ℝ, |F y| ≤ C / (1 + |y|) ^ 2)
    (hV₀ : IntegrableOn (fun y ↦ |deriv F y|) (Ioi 0))
    (hV₁ : IntegrableOn (fun y ↦ logPlus y * |deriv F y|) (Ioi 0))
    (M : ℝ) (hM : ∀ y, |F y| ≤ M) (D : ℝ) (hD : 0 < D) :
    Summable (weightedZeroNorm F D) ∧
    D * (∑' ρ : nontrivialZeros, weightedZeroNorm F D ρ) ≤
      fourierMass F * Real.log (1 / D) + logMoment F + 2 * D * M +
        2 * D * ((3 + 0.15 * logPlus (2 * Real.pi / D)) * totalVariation F +
          0.15 * logVariation F) := by
  classical
  obtain ⟨C, hdecay⟩ := hdecay
  have hC₀ : 0 ≤ C := by simpa using (abs_nonneg (F 0)).trans (hdecay 0)
  let δ := D / (2 * Real.pi)
  let φ : ℝ → ℝ := fun t ↦ |F (δ * t)|
  let m : nontrivialZeros → ℝ := positiveWeight φ
  have hδ : 0 < δ := div_pos hD (by positivity)
  have hφ : ∀ t, 0 ≤ φ t := fun t ↦ abs_nonneg _
  have hφ₀ : φ 0 ≤ M := by simpa [φ] using hM 0
  have hM₀ : 0 ≤ M := (hφ 0).trans hφ₀
  have hInt₁ := fourier_integrableOn_Ioi hC.continuous hC₀ hdecay
  have hInt₂ := log_moment_integrableOn_Ioi hC.continuous hC₀ hdecay hM
  obtain ⟨hDensity, hDensitySum⟩ := integral_main_density_scaled heven hInt₁ hInt₂ hD
  obtain ⟨hError, hErrorBound⟩ := integral_error_bound h (hC.differentiable one_ne_zero) hV₀ hV₁ hδ
  let A := (7 / 8 : ℝ) * φ 0 + (∫ t in Ioi (0 : ℝ), mainDensity t * φ t) -
    ∫ t in Ioi (0 : ℝ), countError t * deriv φ t
  have hlim : Tendsto (fun T : ℝ ↦ ∑ ρ ∈ positiveZeros T, (zeroMultiplicity ρ : ℝ) * φ ρ.im)
      atTop (𝓝 A) := by
    have hboundary := tendsto_countError_absScaled h hδ hC₀ hdecay
    have hden := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hDensity tendsto_id
    have herr := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hError tendsto_id
    have htotal := ((hboundary.add (tendsto_const_nhds (x := (7 / 8 : ℝ) * φ 0))).add hden).sub herr
    rw [zero_add] at htotal
    refine htotal.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact (countError_summation_by_parts φ hT (absScaled_absContinuous hC δ T)).symm
  have hnonneg : 0 ≤ m := by
    intro ρ
    dsimp only [m, positiveWeight]
    split <;> positivity
  have hsumBd (u : Finset nontrivialZeros) : ∑ ρ ∈ u, m ρ ≤ A := by
    apply ge_of_tendsto hlim
    have hlarge : ∀ᶠ T : ℝ in atTop, ∀ ρ ∈ u, (ρ : ℂ).im ≤ T :=
      (eventually_all_finset u).mpr fun ρ _ ↦ eventually_ge_atTop (ρ : ℂ).im
    exact hlarge.mono fun _ hT ↦ positiveWeight_finset_le φ hφ u hT
  have hm : Summable m := summable_of_sum_le hnonneg hsumBd
  have hmBd : ∑' ρ, m ρ ≤ A := Real.tsum_le_of_sum_le hnonneg hsumBd
  have hmr : Summable (fun ρ ↦ m (reflectZero ρ)) := reflectZero.summable_iff.mpr hm
  have hpair : ∀ ρ, weightedZeroNorm F D ρ = m ρ + m (reflectZero ρ) :=
    zeroWeight_eq_pos_pair hRH heven D
  have hsum : Summable (weightedZeroNorm F D) := (hm.add hmr).congr (fun ρ ↦ (hpair ρ).symm)
  refine ⟨hsum, ?_⟩
  rw [tsum_congr hpair, hm.tsum_add hmr, reflectZero.tsum_eq m, ← two_mul]
  have hφerror : (7 / 8 : ℝ) * φ 0 ≤ M := by linarith
  have hErrBound : -(∫ t in Ioi (0 : ℝ), countError t * deriv φ t) ≤
      (3 + 0.15 * logPlus δ⁻¹) * totalVariation F + 0.15 * logVariation F :=
    (neg_le_abs _).trans hErrorBound
  have hδinv : δ⁻¹ = 2 * Real.pi / D := by dsimp only [δ]; rw [inv_div]
  rw [hδinv] at hErrBound
  calc
    _ ≤ D * (2 * A) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hmBd (by norm_num)) hD.le
    _ ≤ _ := by
      dsimp only [A]
      linarith only [hDensitySum, mul_le_mul_of_nonneg_left hφerror (show 0 ≤ 2 * D by positivity),
        mul_le_mul_of_nonneg_left hErrBound (show 0 ≤ 2 * D by positivity)]

/-- Absolute summability of the weighted zero terms at every positive scale. -/
theorem weightedZeroNorm_summable (hRH : RiemannHypothesis) (h : CitedFacts) (F : ℝ → ℝ)
    (heven : Function.Even F) (hC : ContDiff ℝ 1 F)
    (hdecay : ∃ C : ℝ, ∀ y : ℝ, |F y| ≤ C / (1 + |y|) ^ 2)
    (hV₀ : IntegrableOn (fun y ↦ |deriv F y|) (Ioi 0))
    (hV₁ : IntegrableOn (fun y ↦ logPlus y * |deriv F y|) (Ioi 0))
    (M : ℝ) (hM : ∀ y, |F y| ≤ M) (D : ℝ) (hD : 0 < D) :
    Summable (weightedZeroNorm F D) :=
  (zero_sum_bound_logPlus hRH h F heven hC hdecay hV₀ hV₁ M hM D hD).1

/-- Lemma 16, with multiplicity, two-sided ordinates, and absolutely convergent zero sum. -/
theorem zero_sum_bound (hRH : RiemannHypothesis) (h : CitedFacts) (F : ℝ → ℝ)
    (heven : Function.Even F) (hC : ContDiff ℝ 1 F)
    (hdecay : ∃ C : ℝ, ∀ y : ℝ, |F y| ≤ C / (1 + |y|) ^ 2)
    (hV₀ : IntegrableOn (fun y ↦ |deriv F y|) (Ioi 0))
    (hV₁ : IntegrableOn (fun y ↦ logPlus y * |deriv F y|) (Ioi 0))
    (M : ℝ) (hM : ∀ y, |F y| ≤ M) (D : ℝ) (hD : 0 < D) (hD' : D < 1) :
    Summable (weightedZeroNorm F D) ∧
    D * (∑' ρ : nontrivialZeros, weightedZeroNorm F D ρ) ≤
      fourierMass F * Real.log (1 / D) + logMoment F + 2 * D * M +
        2 * D * ((3 + 0.15 * Real.log (2 * Real.pi / D)) * totalVariation F +
          0.15 * logVariation F) := by
  have hscale : 1 ≤ 2 * Real.pi / D := by
    rw [le_div_iff₀ hD, one_mul]
    linarith [Real.pi_gt_d2]
  simpa only [logPlus, max_eq_left (Real.log_nonneg hscale)] using
    zero_sum_bound_logPlus hRH h F heven hC hdecay hV₀ hV₁ M hM D hD

end Legendre

import Legendre.FourierGridSoundness
import Legendre.LogTailIntegral
import Legendre.Native.FourierGrid
import Legendre.TwelveTailBounds
import Legendre.TwelveVariation
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

namespace Legendre

open Filter MeasureTheory Set
open scoped BigOperators

private theorem log_sixteen_upper : Real.log 16 < 2.773 := by
  rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]
  linarith [Real.log_two_lt_d9]

private theorem rpow_neg_natural (y : ℝ) (hy : 0 ≤ y) (n : ℕ) :
    y ^ (-(n : ℝ)) = (y ^ n)⁻¹ := by rw [Real.rpow_neg hy, Real.rpow_natCast]

private theorem integral_power_tail (p : ℝ) (hp : 0 < p) :
    (∫ y in Ioi (16 : ℝ), y ^ (-p - 1)) = (16 : ℝ) ^ (-p) / p := by
  rw [integral_Ioi_rpow_of_lt (by linarith : -p - 1 < -1) (by norm_num),
    show -p - 1 + 1 = -p by ring, div_neg, neg_div, neg_neg]

private theorem majorized_tail {f g : ℝ → ℝ} (hg : IntegrableOn g (Ioi 16))
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 16)))
    (h : ∀ y > 16, 0 ≤ f y ∧ f y ≤ g y) :
    IntegrableOn f (Ioi 16) ∧ (∫ y in Ioi 16, f y) ≤ ∫ y in Ioi 16, g y := by
  have hfI : IntegrableOn f (Ioi 16) := by
    apply hg.mono' hf
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (h y hy).1]
    exact (h y hy).2
  refine ⟨hfI, integral_mono_ae hfI hg ?_⟩
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
  exact (h y hy).2

private theorem abs_F_tail_rpow (y : ℝ) (hy : 16 ≤ y) :
    |twelveMode.F y| ≤ (0.00000012 : ℝ) * y ^ (-2 : ℝ) + 0.0244 * y ^ (-4 : ℝ) := by
  rw [show (-2 : ℝ) = -(↑(2 : ℕ) : ℝ) by norm_num,
    show (-4 : ℝ) = -(↑(4 : ℕ) : ℝ) by norm_num, rpow_neg_natural y (by linarith),
    rpow_neg_natural y (by linarith), ← div_eq_mul_inv, ← div_eq_mul_inv]
  exact twelveMode_abs_F_tail y hy

private theorem mass_tail : IntegrableOn (fun y ↦ |twelveMode.F y|) (Ioi 16) ∧
    2 * (∫ y in Ioi 16, |twelveMode.F y|) < 0.000004 := by
  have h₂ := (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) (by norm_num : (0 : ℝ) < 16)).const_mul
    (0.00000012 : ℝ)
  have h₄ := (integrableOn_Ioi_rpow_of_lt (a := -4) (by norm_num) (by norm_num : (0 : ℝ) < 16)).const_mul
    (0.0244 : ℝ)
  have h := majorized_tail (h₂.add h₄) twelveMode.F_contDiff_one.continuous.abs.aestronglyMeasurable
    (fun y hy ↦ ⟨abs_nonneg _, abs_F_tail_rpow y hy.le⟩)
  refine ⟨h.1, (mul_le_mul_of_nonneg_left h.2 (by norm_num)).trans_lt ?_⟩
  change 2 * (∫ y in Ioi (16 : ℝ), 0.00000012 * y ^ (-2 : ℝ) + 0.0244 * y ^ (-4 : ℝ)) < _
  rw [integral_add h₂ h₄, integral_const_mul, integral_const_mul,
    show (-2 : ℝ) = -1 - 1 by norm_num, show (-4 : ℝ) = -3 - 1 by norm_num,
    integral_power_tail 1 (by norm_num), integral_power_tail 3 (by norm_num),
    Real.rpow_neg_one, show (-3 : ℝ) = -(↑(3 : ℕ) : ℝ) by norm_num,
    rpow_neg_natural 16 (by norm_num)]
  norm_num

private theorem log_moment_tail : IntegrableOn (fun y ↦ |twelveMode.F y| * Real.log y) (Ioi 16) ∧
    2 * (∫ y in Ioi 16, |twelveMode.F y| * Real.log y) < 0.0000125 := by
  have h₂ := (integrableOn_rpow_mul_log_tail (p := 1) (by norm_num) (by norm_num : (1 : ℝ) ≤ 16)).const_mul
    (0.00000012 : ℝ)
  have h₄ := (integrableOn_rpow_mul_log_tail (p := 3) (by norm_num) (by norm_num : (1 : ℝ) ≤ 16)).const_mul
    (0.0244 : ℝ)
  have h := majorized_tail (h₂.add h₄)
    (twelveMode.F_contDiff_one.continuous.abs.measurable.mul Real.measurable_log).aestronglyMeasurable
    (fun y hy ↦ ?_)
  · refine ⟨h.1, (mul_le_mul_of_nonneg_left h.2 (by norm_num)).trans_lt ?_⟩
    change 2 * (∫ y in Ioi (16 : ℝ),
      0.00000012 * (y ^ (-1 - 1 : ℝ) * Real.log y) + 0.0244 * (y ^ (-3 - 1 : ℝ) * Real.log y)) < _
    rw [integral_add h₂ h₄, integral_const_mul, integral_const_mul, integral_rpow_mul_log_tail (by norm_num)
      (by norm_num), integral_rpow_mul_log_tail (by norm_num) (by norm_num), Real.rpow_neg_one,
      show (-3 : ℝ) = -(↑(3 : ℕ) : ℝ) by norm_num, rpow_neg_natural 16 (by norm_num)]
    norm_num
    linarith only [log_sixteen_upper]
  · have hpos := Real.log_nonneg (show 1 ≤ y by linarith)
    refine ⟨mul_nonneg (abs_nonneg _) hpos, ?_⟩
    convert mul_le_mul_of_nonneg_right (abs_F_tail_rpow y hy.le) hpos using 1
    norm_num
    ring

private theorem integral_split_mass : fourierMass twelveMode.F =
    2 * ((∫ y in (0 : ℝ)..16, |twelveMode.F y|) + ∫ y in Ioi 16, |twelveMode.F y|) := by
  have hEven (y : ℝ) : twelveMode.F |y| = twelveMode.F y := by
    rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hy]
    · rw [abs_of_neg hy, twelveMode.F_even y]
  have hsplit := intervalIntegral.integral_interval_add_Ioi'
    (twelveMode.F_contDiff_one.continuous.abs.intervalIntegrable 0 16) mass_tail.1
  unfold fourierMass
  calc
    _ = (∫ y, |twelveMode.F (|y|)|) := by simp only [hEven]
    _ = _ := by rw [integral_comp_abs (f := fun y ↦ |twelveMode.F y|), ← hsplit]

private theorem integral_split_moment : logMoment twelveMode.F =
    2 * ((∫ y in (0 : ℝ)..16, |twelveMode.F y| * Real.log y) + ∫ y in Ioi 16, |twelveMode.F y| * Real.log y) := by
  have hEven (y : ℝ) : twelveMode.F |y| = twelveMode.F y := by
    rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hy]
    · rw [abs_of_neg hy, twelveMode.F_even y]
  have hInt := (intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 16)).continuousOn_mul
    twelveMode.F_contDiff_one.continuous.abs.continuousOn
  have hsplit := intervalIntegral.integral_interval_add_Ioi' hInt log_moment_tail.1
  unfold logMoment
  calc
    _ = (∫ y, |twelveMode.F (|y|)| * Real.log |y|) := by simp only [hEven]
    _ = _ := by rw [integral_comp_abs (f := fun y ↦ |twelveMode.F y| * Real.log y), ← hsplit]

private theorem twelveMode_totalVariation : totalVariation twelveMode.F < 625 := by
  have hg := (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) (by norm_num : (0 : ℝ) < 16)).const_mul (64 : ℝ)
  have hc := (contDiff_one_iff_deriv.mp twelveMode.F_contDiff_one).2.abs
  have htail := majorized_tail hg hc.aestronglyMeasurable (fun y hy ↦ ⟨abs_nonneg _, by
    simpa only [show (-2 : ℝ) = -(↑(2 : ℕ) : ℝ) by norm_num, rpow_neg_natural y (by linarith : 0 ≤ y),
      ← div_eq_mul_inv] using twelveMode_abs_deriv_tail y hy.le⟩)
  have htail' := htail.2
  rw [integral_const_mul, show (-2 : ℝ) = -1 - 1 by norm_num,
    integral_power_tail 1 (by norm_num), Real.rpow_neg_one] at htail'
  have hcore : (∫ y in (0 : ℝ)..16, |deriv twelveMode.F y|) ≤ 19 * 16 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 16)
      (C := 19) (f := fun y ↦ |deriv twelveMode.F y|) (fun y _ ↦ by
        simpa only [Real.norm_eq_abs, abs_abs] using twelveMode_abs_deriv_core y)
    exact (le_abs_self _).trans (by simpa using h)
  unfold totalVariation
  rw [← intervalIntegral.integral_interval_add_Ioi' (hc.intervalIntegrable 0 16) htail.1]
  linarith

private theorem twelveMode_logVariation : logVariation twelveMode.F < 2000 := by
  have hc := (contDiff_one_iff_deriv.mp twelveMode.F_contDiff_one).2.abs
  have htail₀ := (integrableOn_rpow_mul_log_tail (p := 1) (by norm_num) (by norm_num : (1 : ℝ) ≤ 16)).const_mul (64 : ℝ)
  have htail := majorized_tail (f := fun y ↦ logPlus y * |deriv twelveMode.F y|) htail₀
    ((Real.measurable_log.max (measurable_const (a := (0 : ℝ)))).mul hc.measurable).aestronglyMeasurable
    (fun y hy ↦ ?_)
  · have htail' := htail.2
    rw [integral_const_mul, integral_rpow_mul_log_tail (by norm_num) (by norm_num), Real.rpow_neg_one] at htail'
    have hcore : (∫ y in (0 : ℝ)..16, logPlus y * |deriv twelveMode.F y|) ≤ (2.773 * 19) * 16 := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 16)
        (C := 2.773 * 19) (f := fun y ↦ logPlus y * |deriv twelveMode.F y|) (fun y hy ↦ ?_)
      · exact (le_abs_self _).trans (by simpa using h)
      · rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 16)] at hy
        have hlog : logPlus y ≤ 2.773 := max_le
          ((Real.log_le_log hy.1 hy.2).trans log_sixteen_upper.le) (by norm_num)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (abs_nonneg _))]
        exact mul_le_mul hlog (twelveMode_abs_deriv_core y) (abs_nonneg _) (by norm_num)
    have hInt : IntervalIntegrable (fun y ↦ logPlus y * |deriv twelveMode.F y|) volume 0 16 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 16)).mpr
        (twelveMode.derivative_integration_bounds.2.mono_set Ioc_subset_Ioi_self)
    unfold logVariation
    rw [← intervalIntegral.integral_interval_add_Ioi' hInt htail.1]
    linarith [log_sixteen_upper]
  · have hlog : 0 ≤ Real.log y := Real.log_nonneg (show 1 ≤ y by linarith)
    simp only [logPlus, max_eq_left hlog]
    refine ⟨mul_nonneg hlog (abs_nonneg _), ?_⟩
    calc
      _ ≤ Real.log y * (64 / y ^ 2) := mul_le_mul_of_nonneg_left (twelveMode_abs_deriv_tail y hy.le) hlog
      _ = _ := by rw [show (-1 - 1 : ℝ) = -(↑(2 : ℕ) : ℝ) by norm_num,
        rpow_neg_natural y (by linarith)]; ring

/-- Lemma 19. All numerical and analytic estimates for the twelve-mode test. -/
theorem twelve_mode_bounds : TwelveModeEstimates := by
  refine ⟨twelveMode_F_zero_lower, ?_, ?_, twelveMode_totalVariation, twelveMode_logVariation⟩
  · rw [integral_split_mass]
    have h := checkGridMass_integral_sound 0.7658655 grid_mass_verified
    norm_num at h
    linarith [mass_tail.2]
  · rw [integral_split_moment]
    have h := checkGridMoment_integral_sound (-1.379585) grid_moment_verified
    norm_num at h
    linarith [log_moment_tail.2]

end Legendre

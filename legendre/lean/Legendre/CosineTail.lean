import Legendre.Cosine
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace Legendre.CosineTest

open Filter MeasureTheory Set
open scoped BigOperators

private theorem oscillatory_integral_bound {a b t C : ℝ} (hab : a ≤ b)
    {u u' u'' v v' : ℝ → ℝ}
    (hu : ∀ s, HasDerivAt u (u' s) s) (hu' : ∀ s, HasDerivAt u' (u'' s) s)
    (hv : ∀ s, HasDerivAt v (v' s) s) (hv' : ∀ s, HasDerivAt v' (-t ^ 2 * v s) s)
    (hu'' : Continuous u'') (ha : u a = 0) (hb : u b = 0)
    (hC : ∀ s ∈ Icc a b, |u'' s| ≤ C) (hV : ∀ s, |v s| ≤ 1) :
    t ^ 2 * |∫ s in a..b, u s * v s| ≤ |u' b| + |u' a| + C * (b - a) := by
  have hcont_u' : Continuous u' := continuous_iff_continuousAt.mpr fun s ↦ (hu' s).continuousAt
  have hcont_v : Continuous v := continuous_iff_continuousAt.mpr fun s ↦ (hv s).continuousAt
  have hcont_v' : Continuous v' := continuous_iff_continuousAt.mpr fun s ↦ (hv' s).continuousAt
  have h₁ := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun s _ ↦ hu s) (fun s _ ↦ hv' s) (hcont_u'.intervalIntegrable a b)
    ((hcont_v.const_mul (-t ^ 2)).intervalIntegrable a b)
  have h₂ := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun s _ ↦ hu' s) (fun s _ ↦ hv s) (hu''.intervalIntegrable a b)
    (hcont_v'.intervalIntegrable a b)
  have hmul : (∫ s in a..b, u s * (-t ^ 2 * v s)) = -t ^ 2 * (∫ s in a..b, u s * v s) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext s
    ring
  rw [hmul, ha, hb, zero_mul, zero_mul, sub_self, zero_sub, h₂] at h₁
  have hEq : t ^ 2 * (∫ s in a..b, u s * v s) =
      u' b * v b - u' a * v a - ∫ s in a..b, u'' s * v s := by linarith only [h₁]
  have hInt : |∫ s in a..b, u'' s * v s| ≤ C * (b - a) := by
    have hl := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (C := C) (f := fun s ↦ u'' s * v s) (fun s hs ↦ ?_)
    · simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using hl
    · rw [uIoc_of_le hab] at hs
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hV s)).trans (hC s (Ioc_subset_Icc_self hs))
  rw [← abs_of_nonneg (sq_nonneg t), ← abs_mul, hEq]
  apply (abs_sub _ _).trans
  apply add_le_add _ hInt
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hV b)
  · rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hV a)

private theorem hasDerivAt_sin_frequency (t s : ℝ) :
    HasDerivAt (fun s ↦ Real.sin (t * s)) (t * Real.cos (t * s)) s := by
  simpa [mul_comm] using (Real.hasDerivAt_sin (t * s)).comp s ((hasDerivAt_id s).const_mul t)

private theorem hasDerivAt_cos_frequency (t s : ℝ) :
    HasDerivAt (fun s ↦ Real.cos (t * s)) (-(t * Real.sin (t * s))) s := by
  simpa [mul_comm] using (Real.hasDerivAt_cos (t * s)).comp s ((hasDerivAt_id s).const_mul t)

private theorem oscillatory_integral_bound_cos {a b t C : ℝ} (hab : a ≤ b)
    {u u' u'' : ℝ → ℝ}
    (hu : ∀ s, HasDerivAt u (u' s) s) (hu' : ∀ s, HasDerivAt u' (u'' s) s)
    (hu'' : Continuous u'') (ha : u a = 0) (hb : u b = 0)
    (hC : ∀ s ∈ Icc a b, |u'' s| ≤ C) :
    t ^ 2 * |∫ s in a..b, u s * Real.cos (t * s)| ≤ |u' b| + |u' a| + C * (b - a) := by
  refine oscillatory_integral_bound hab hu hu' (hasDerivAt_cos_frequency t) (fun s ↦ ?_)
    hu'' ha hb hC (fun s ↦ Real.abs_cos_le_one _)
  exact ((hasDerivAt_sin_frequency t s).const_mul t).neg.congr_deriv (by ring)

private theorem oscillatory_integral_bound_sin {a b t C : ℝ} (hab : a ≤ b)
    {u u' u'' : ℝ → ℝ}
    (hu : ∀ s, HasDerivAt u (u' s) s) (hu' : ∀ s, HasDerivAt u' (u'' s) s)
    (hu'' : Continuous u'') (ha : u a = 0) (hb : u b = 0)
    (hC : ∀ s ∈ Icc a b, |u'' s| ≤ C) :
    t ^ 2 * |∫ s in a..b, u s * Real.sin (t * s)| ≤ |u' b| + |u' a| + C * (b - a) := by
  refine oscillatory_integral_bound hab hu hu' (hasDerivAt_sin_frequency t) (fun s ↦ ?_)
    hu'' ha hb hC (fun s ↦ Real.abs_sin_le_one _)
  exact ((hasDerivAt_cos_frequency t s).const_mul t).congr_deriv (by ring)

private theorem bounded_sq_mul_F (g : CosineTest) : ∃ C : ℝ, ∀ y : ℝ, y ^ 2 * |g.F y| ≤ C := by
  have hderiv := g.contDiff_polynomial.differentiable (by norm_num)
  have hderiv' := g.contDiff_polynomial.differentiable_deriv_two
  have hcont : Continuous (deriv (deriv g.polynomial)) := by
    have h := (contDiff_succ_iff_deriv.mp
      (show ContDiff ℝ (1 + 1) g.polynomial from g.contDiff_polynomial)).2.2
    exact (contDiff_one_iff_deriv.mp h).2
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-g.K) g.K)).bddAbove_image
    hcont.abs.continuousOn
  let B := |deriv g.polynomial g.K| + |deriv g.polynomial (-g.K)| + C * (g.K - (-g.K))
  refine ⟨B / (2 * Real.pi) ^ 2, fun y ↦ ?_⟩
  have h := oscillatory_integral_bound_cos (t := 2 * Real.pi * y) (by linarith [g.K_pos] : -g.K ≤ g.K)
    (fun s ↦ (hderiv s).hasDerivAt) (fun s ↦ (hderiv' s).hasDerivAt) hcont
    g.polynomial_neg_endpoint g.polynomial_pos_endpoint (fun s hs ↦ hC ⟨s, hs, rfl⟩)
  change (2 * Real.pi * y) ^ 2 * |g.F y| ≤ B at h
  apply (le_div_iff₀ (by positivity)).mpr
  convert h using 1
  ring

theorem F_decay (g : CosineTest) : ∃ C : ℝ, ∀ y : ℝ, |g.F y| ≤ C / (1 + |y|) ^ 2 := by
  obtain ⟨B, hB⟩ := g.bounded_sq_mul_F
  use 4 * max B g.mass
  intro y
  have hpos : 0 < (1 + |y|) ^ 2 := by positivity
  apply (le_div_iff₀ hpos).mpr
  by_cases hy : |y| ≤ 1
  · have hs : (1 + |y|) ^ 2 ≤ (2 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    calc
      _ ≤ |g.F y| * 2 ^ 2 := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ ≤ g.mass * 2 ^ 2 := mul_le_mul_of_nonneg_right (g.abs_F_le_mass y) (by norm_num)
      _ ≤ _ := by nlinarith only [le_max_right B g.mass]
  · have hs : (1 + |y|) ^ 2 ≤ (2 * |y|) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith [lt_of_not_ge hy]) 2
    calc
      _ ≤ |g.F y| * (2 * |y|) ^ 2 := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
      _ = 4 * (y ^ 2 * |g.F y|) := by rw [mul_pow, sq_abs]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ((hB y).trans (le_max_left _ _)) (by norm_num)

theorem sq_mul_abs_deriv_F_bound (g : CosineTest) (C : ℝ)
    (hC : ∀ s ∈ Icc (-g.K) g.K, |deriv (deriv (fun u : ℝ ↦ u * g.polynomial u)) s| ≤ C)
    (y : ℝ) :
    y ^ 2 * |deriv g.F y| ≤
      (|deriv (fun u : ℝ ↦ u * g.polynomial u) g.K| + |deriv (fun u : ℝ ↦ u * g.polynomial u) (-g.K)| +
        C * (g.K - (-g.K))) / (2 * Real.pi) := by
  let u : ℝ → ℝ := fun s ↦ s * g.polynomial s
  have hu : ContDiff ℝ 2 u := by exact contDiff_id.mul g.contDiff_polynomial
  have hu₁ := hu.differentiable (by norm_num)
  have hu₂ := hu.differentiable_deriv_two
  have hcont : Continuous (deriv (deriv u)) := by
    have h := (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) u from hu)).2.2
    exact (contDiff_one_iff_deriv.mp h).2
  have h := oscillatory_integral_bound_sin (t := 2 * Real.pi * y) (by linarith [g.K_pos] : -g.K ≤ g.K)
    (fun s ↦ (hu₁ s).hasDerivAt) (fun s ↦ (hu₂ s).hasDerivAt) hcont
    (by simp [u, g.polynomial_neg_endpoint]) (by simp [u, g.polynomial_pos_endpoint])
    hC
  have heq : deriv g.F y = -(2 * Real.pi) * ∫ s in -g.K..g.K, u s * Real.sin (2 * Real.pi * y * s) := by
    rw [g.deriv_F y, ← intervalIntegral.integral_const_mul]
    congr 1
    funext s
    rw [show 2 * Real.pi * s * y = 2 * Real.pi * y * s by ring]
    dsimp [u]
    ring
  rw [heq, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  apply (le_div_iff₀ (by positivity)).mpr
  convert h using 1
  ring

private theorem bounded_sq_mul_deriv_F (g : CosineTest) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ y : ℝ, y ^ 2 * |deriv g.F y| ≤ C := by
  let u : ℝ → ℝ := fun s ↦ s * g.polynomial s
  have hu : ContDiff ℝ 2 u := contDiff_id.mul g.contDiff_polynomial
  have hcont : Continuous (deriv (deriv u)) :=
    (contDiff_one_iff_deriv.mp (contDiff_succ_iff_deriv.mp
      (show ContDiff ℝ (1 + 1) u from hu)).2.2).2
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-g.K) g.K)).bddAbove_image hcont.abs.continuousOn
  let B := (|deriv u g.K| + |deriv u (-g.K)| + C * (g.K - (-g.K))) / (2 * Real.pi)
  exact ⟨max 0 B, le_max_left _ _, fun y ↦
    (g.sq_mul_abs_deriv_F_bound C (fun s hs ↦ hC ⟨s, hs, rfl⟩) y).trans (le_max_right _ _)⟩

theorem derivative_integration_bounds (g : CosineTest) :
    IntegrableOn (fun y ↦ |deriv g.F y|) (Ioi 0) ∧
      IntegrableOn (fun y ↦ logPlus y * |deriv g.F y|) (Ioi 0) := by
  obtain ⟨C, hC, hbound⟩ := g.bounded_sq_mul_deriv_F
  have hAbs : Continuous (fun y ↦ |deriv g.F y|) := (contDiff_one_iff_deriv.mp g.F_contDiff_one).2.abs
  have hderivative (y : ℝ) (hy : 1 < y) : |deriv g.F y| ≤ C * y ^ (-2 : ℝ) := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by positivity),
      Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    simpa [mul_comm] using hbound y
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union, integrableOn_union]
  constructor
  · refine ⟨(hAbs.intervalIntegrable 0 1).1, ?_⟩
    apply Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul C) hAbs.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
    simpa only [Real.norm_eq_abs, abs_abs] using hderivative y hy
  · constructor
    · have hzero : IntegrableOn (fun _ : ℝ ↦ (0 : ℝ)) (Ioc 0 1) := integrableOn_zero
      apply hzero.congr_fun _ measurableSet_Ioc
      intro y hy
      change (0 : ℝ) = logPlus y * |deriv g.F y|
      rw [logPlus, max_eq_right (Real.log_nonpos hy.1.le hy.2), zero_mul]
    · have hcont : AEStronglyMeasurable (fun y ↦ logPlus y * |deriv g.F y|)
          (volume.restrict (Ioi 1)) :=
        (((Real.measurable_log.max measurable_const).mul hAbs.measurable)).aestronglyMeasurable
      apply Integrable.mono' ((integrableOn_Ioi_rpow_of_lt
        (by norm_num : (-3 / 2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)).const_mul (2 * C)) hcont
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
      have hy₀ : 0 < y := zero_lt_one.trans hy
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (abs_nonneg _)),
        logPlus, max_eq_left (Real.log_nonneg hy.le)]
      calc
        _ ≤ (y ^ (1 / 2 : ℝ) / (1 / 2)) * (C * y ^ (-2 : ℝ)) :=
          mul_le_mul (Real.log_le_rpow_div hy₀.le (by norm_num)) (hderivative y hy)
            (abs_nonneg _) (by positivity)
        _ = (2 * C) * y ^ (-3 / 2 : ℝ) := by
          rw [show -3 / 2 = (1 / 2 : ℝ) + (-2) by norm_num, Real.rpow_add hy₀]
          ring

end Legendre.CosineTest

namespace Legendre

open MeasureTheory Set

/-- Lemma 13, including the decay and variation bounds needed in the zero sum. -/
theorem cosine_fourier_spec (g : CosineTest) :
    Function.Even g.G ∧ (∃ C : NNReal, LipschitzWith C g.G) ∧
    g.G (-g.K) = 0 ∧ g.G g.K = 0 ∧ (∀ s, |g.G s| ≤ g.weightSum) ∧
    Integrable g.G ∧ g.mass ≤ 2 * g.K * g.weightSum ∧
    Function.Even g.F ∧ Differentiable ℂ g.complexF ∧
    (∀ y : ℝ, g.complexF y = (g.F y : ℂ)) ∧ g.F 0 = (∫ s, g.G s) ∧
    (∀ y : ℝ, (∀ j : Fin g.modes, (CosineTest.frequency j : ℝ) ^ 2 ≠ (4 * g.K * y) ^ 2) →
      g.F y = 4 * g.K / Real.pi * Real.cos (2 * Real.pi * g.K * y) *
        ∑ j : Fin g.modes,
          (-1 : ℝ) ^ j.val * CosineTest.frequency j * g.weight j /
            ((CosineTest.frequency j : ℝ) ^ 2 - (4 * g.K * y) ^ 2)) ∧
    (∀ j, g.F ((CosineTest.frequency j : ℝ) / (4 * g.K)) = g.K * g.weight j) ∧
    (∃ C : ℝ, ∀ y : ℝ, |g.F y| ≤ C / (1 + |y|) ^ 2) ∧
    ContDiff ℝ 1 g.F ∧
    IntegrableOn (fun y ↦ |deriv g.F y|) (Ioi 0) ∧
    IntegrableOn (fun y ↦ logPlus y * |deriv g.F y|) (Ioi 0) ∧
    (∀ y, |g.F y| ≤ g.mass ∧ |deriv g.F y| ≤ 2 * Real.pi * g.K ^ 2 * g.weightSum) :=
  ⟨g.G_even, g.G_lipschitz, g.G_endpoints.1, g.G_endpoints.2, g.abs_G_le_weightSum,
    g.G_integrable, g.mass_le, g.F_even, g.differentiable_complexF, g.complexF_ofReal, g.F_zero,
    g.F_eq_closed_form, g.F_angular_value, g.F_decay, g.F_contDiff_one,
    g.derivative_integration_bounds.1, g.derivative_integration_bounds.2,
    fun y ↦ ⟨g.abs_F_le_mass y, g.abs_deriv_F_le y⟩⟩

end Legendre

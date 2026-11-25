import Legendre.AnalyticData
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Legendre.CosineTest

open Filter MeasureTheory Set
open scoped BigOperators NNReal Topology

private theorem neg_K_le_K (g : CosineTest) : -g.K ≤ g.K := by linarith [g.K_pos]

noncomputable def angularFrequency (g : CosineTest) (j : Fin g.modes) : ℝ :=
  Real.pi * frequency j / (2 * g.K)

theorem polynomial_eq_sum (g : CosineTest) (s : ℝ) :
    g.polynomial s = ∑ j, g.weight j * Real.cos (g.angularFrequency j * s) := by
  unfold polynomial angularFrequency
  congr 1
  ext j
  rw [div_mul_eq_mul_div]

@[fun_prop] theorem continuous_polynomial (g : CosineTest) : Continuous g.polynomial := by
  simp_rw [show g.polynomial = fun s ↦ ∑ j, g.weight j * Real.cos (g.angularFrequency j * s)
    from funext g.polynomial_eq_sum]
  fun_prop

theorem contDiff_polynomial (g : CosineTest) : ContDiff ℝ 2 g.polynomial := by
  simp_rw [show g.polynomial = fun s ↦ ∑ j, g.weight j * Real.cos (g.angularFrequency j * s)
    from funext g.polynomial_eq_sum]
  fun_prop

theorem polynomial_even (g : CosineTest) : Function.Even g.polynomial := by
  intro s
  simp only [polynomial_eq_sum, mul_neg, Real.cos_neg]

private theorem angularFrequency_mul_K (g : CosineTest) (j : Fin g.modes) :
    g.angularFrequency j * g.K = Real.pi / 2 + (j.val : ℝ) * Real.pi := by
  unfold angularFrequency frequency
  push_cast
  field_simp [g.K_pos.ne']
  ring

theorem polynomial_pos_endpoint (g : CosineTest) : g.polynomial g.K = 0 := by
  rw [polynomial_eq_sum]
  simp only [angularFrequency_mul_K, Real.cos_add_nat_mul_pi, Real.cos_pi_div_two,
    mul_zero, Finset.sum_const_zero]

theorem polynomial_neg_endpoint (g : CosineTest) : g.polynomial (-g.K) = 0 :=
  (g.polynomial_even g.K).trans g.polynomial_pos_endpoint

theorem G_eq_polynomial (g : CosineTest) {s : ℝ} (hs : s ∈ Icc (-g.K) g.K) :
    g.G s = g.polynomial s := by simp [G, hs]

theorem G_eq_zero (g : CosineTest) {s : ℝ} (hs : s ∉ Icc (-g.K) g.K) :
    g.G s = 0 := by simp [G, hs]

theorem G_endpoints (g : CosineTest) : g.G (-g.K) = 0 ∧ g.G g.K = 0 := by
  exact ⟨(g.G_eq_polynomial ⟨le_rfl, g.neg_K_le_K⟩).trans g.polynomial_neg_endpoint,
    (g.G_eq_polynomial ⟨g.neg_K_le_K, le_rfl⟩).trans g.polynomial_pos_endpoint⟩

theorem G_even (g : CosineTest) : Function.Even g.G := by
  intro s
  have hs : -s ∈ Icc (-g.K) g.K ↔ s ∈ Icc (-g.K) g.K := by
    simp only [mem_Icc]
    constructor <;> intro h <;> exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
  by_cases h : s ∈ Icc (-g.K) g.K
  · rw [g.G_eq_polynomial (hs.mpr h), g.G_eq_polynomial h, g.polynomial_even]
  · rw [g.G_eq_zero (mt hs.mp h), g.G_eq_zero h]

theorem weightSum_nonneg (g : CosineTest) : 0 ≤ g.weightSum :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

theorem abs_polynomial_le_weightSum (g : CosineTest) (s : ℝ) :
    |g.polynomial s| ≤ g.weightSum := by
  rw [polynomial_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

theorem abs_G_le_weightSum (g : CosineTest) (s : ℝ) : |g.G s| ≤ g.weightSum := by
  by_cases h : s ∈ Icc (-g.K) g.K
  · rw [g.G_eq_polynomial h]
    exact g.abs_polynomial_le_weightSum s
  · simpa [g.G_eq_zero h] using g.weightSum_nonneg

theorem hasDerivAt_polynomial (g : CosineTest) (s : ℝ) :
    HasDerivAt g.polynomial
      (∑ j, g.weight j * (-Real.sin (g.angularFrequency j * s) * g.angularFrequency j)) s := by
  simp_rw [show g.polynomial = fun t ↦ ∑ j, g.weight j * Real.cos (g.angularFrequency j * t)
    from funext g.polynomial_eq_sum]
  exact HasDerivAt.fun_sum fun j _ ↦
    (((Real.hasDerivAt_cos _).comp s ((hasDerivAt_id s).const_mul _)).const_mul _).congr_deriv
      (by simp)

theorem deriv_polynomial (g : CosineTest) (s : ℝ) :
    deriv g.polynomial s =
      ∑ j, g.weight j * (-Real.sin (g.angularFrequency j * s) * g.angularFrequency j) :=
  (g.hasDerivAt_polynomial s).deriv

theorem hasDerivAt_deriv_polynomial (g : CosineTest) (s : ℝ) :
    HasDerivAt (deriv g.polynomial)
      (∑ j, -(g.weight j * Real.cos (g.angularFrequency j * s) * g.angularFrequency j ^ 2)) s := by
  simp_rw [show deriv g.polynomial = fun t ↦ ∑ j,
    g.weight j * (-Real.sin (g.angularFrequency j * t) * g.angularFrequency j)
    from funext g.deriv_polynomial]
  refine HasDerivAt.fun_sum fun j _ ↦ ?_
  have h₁ := (Real.hasDerivAt_sin (g.angularFrequency j * s)).comp s
    ((hasDerivAt_id s).const_mul (g.angularFrequency j))
  have h₂ := (h₁.neg.mul_const (g.angularFrequency j)).const_mul (g.weight j)
  exact h₂.congr_deriv (by simp; ring)

theorem abs_deriv_deriv_polynomial_le (g : CosineTest) (s : ℝ) :
    |deriv (deriv g.polynomial) s| ≤ ∑ j, |g.weight j| * g.angularFrequency j ^ 2 := by
  rw [(g.hasDerivAt_deriv_polynomial s).deriv]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (g.angularFrequency j))]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)) (sq_nonneg _)

theorem polynomial_lipschitz (g : CosineTest) : ∃ C : ℝ≥0, LipschitzWith C g.polynomial := by
  let c : ℝ := ∑ j, |g.weight j| * |g.angularFrequency j|
  have hc : 0 ≤ c := Finset.sum_nonneg fun _ _ ↦ by positivity
  refine ⟨⟨c, hc⟩, lipschitzWith_of_nnnorm_deriv_le
    (fun s ↦ (g.hasDerivAt_polynomial s).differentiableAt) fun s ↦ ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, g.deriv_polynomial]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [abs_mul, abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)) (abs_nonneg _)

theorem G_lipschitz (g : CosineTest) : ∃ C : ℝ≥0, LipschitzWith C g.G := by
  obtain ⟨C, hC⟩ := g.polynomial_lipschitz
  have hclip : LipschitzWith 1 (fun s : ℝ ↦ max (-g.K) (min s g.K)) :=
    (LipschitzWith.id.min_const g.K).const_max (-g.K)
  refine ⟨C, ?_⟩
  have eq_clip : g.G = g.polynomial ∘ (fun s : ℝ ↦ max (-g.K) (min s g.K)) := by
    ext s
    simp only [Function.comp_apply]
    by_cases h₁ : s < -g.K
    · rw [g.G_eq_zero (fun h ↦ (not_le_of_gt h₁) h.1), min_eq_left (le_trans h₁.le g.neg_K_le_K),
        max_eq_left h₁.le, g.polynomial_neg_endpoint]
    by_cases h₂ : g.K < s
    · rw [g.G_eq_zero (fun h ↦ (not_le_of_gt h₂) h.2), min_eq_right h₂.le,
        max_eq_right g.neg_K_le_K, g.polynomial_pos_endpoint]
    have hs : s ∈ Icc (-g.K) g.K := ⟨le_of_not_gt h₁, le_of_not_gt h₂⟩
    rw [g.G_eq_polynomial hs, min_eq_left hs.2, max_eq_right hs.1]
  rw [eq_clip]
  simpa only [mul_one] using hC.comp hclip

theorem G_integrable (g : CosineTest) : Integrable g.G := by
  rw [G, integrable_indicator_iff measurableSet_Icc]
  exact g.continuous_polynomial.continuousOn.integrableOn_compact isCompact_Icc

theorem mass_eq_interval (g : CosineTest) :
    g.mass = ∫ s in -g.K..g.K, |g.polynomial s| := by
  rw [mass, intervalIntegral.integral_of_le g.neg_K_le_K, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  congr 1
  ext s
  by_cases hs : s ∈ Icc (-g.K) g.K <;> simp [G, hs]

theorem mass_le (g : CosineTest) : g.mass ≤ 2 * g.K * g.weightSum := by
  rw [g.mass_eq_interval]
  calc
    (∫ s in -g.K..g.K, |g.polynomial s|) ≤ ∫ _ in -g.K..g.K, g.weightSum :=
      intervalIntegral.integral_mono_on g.neg_K_le_K
        (g.continuous_polynomial.abs.intervalIntegrable _ _)
        intervalIntegrable_const (fun s _ ↦ g.abs_polynomial_le_weightSum s)
    _ = 2 * g.K * g.weightSum := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

theorem F_even (g : CosineTest) : Function.Even g.F := by
  intro y
  unfold F
  simp only [mul_neg, neg_mul, Real.cos_neg]

theorem F_zero (g : CosineTest) : g.F 0 = ∫ s, g.G s := by
  simp only [F, mul_zero, zero_mul, Real.cos_zero, mul_one, G,
    integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le g.neg_K_le_K]

theorem abs_F_le_mass (g : CosineTest) (y : ℝ) : |g.F y| ≤ g.mass := by
  rw [F, g.mass_eq_interval]
  apply (intervalIntegral.abs_integral_le_integral_abs g.neg_K_le_K).trans
  have hc : Continuous fun s ↦ |g.polynomial s * Real.cos (2 * Real.pi * y * s)| := by
    fun_prop
  apply intervalIntegral.integral_mono_on g.neg_K_le_K (hc.intervalIntegrable _ _)
    (g.continuous_polynomial.abs.intervalIntegrable _ _)
  intro s _
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

private theorem integral_scaled_cos (K c : ℝ) (hc : c ≠ 0) :
    (∫ s in -K..K, Real.cos (c * s)) = 2 * Real.sin (c * K) / c := by
  rw [intervalIntegral.integral_comp_mul_left _ hc, integral_cos, mul_neg, Real.sin_neg, smul_eq_mul]
  ring

private theorem integral_cos_product (K a b : ℝ) :
    (∫ s in -K..K, Real.cos (a * s) * Real.cos (b * s)) =
      ((∫ s in -K..K, Real.cos ((a - b) * s)) + (∫ s in -K..K, Real.cos ((a + b) * s))) / 2 := by
  calc
    _ = ∫ s in -K..K, (Real.cos ((a - b) * s) + Real.cos ((a + b) * s)) * (2 : ℝ)⁻¹ := by
      congr 1
      funext s
      rw [show (a - b) * s = a * s - b * s by ring,
        show (a + b) * s = a * s + b * s by ring, ← Real.two_mul_cos_mul_cos]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_add]
      · ring
      · exact (show Continuous fun s ↦ Real.cos ((a - b) * s) by fun_prop).intervalIntegrable _ _
      · exact (show Continuous fun s ↦ Real.cos ((a + b) * s) by fun_prop).intervalIntegrable _ _

theorem F_eq_sum_integrals (g : CosineTest) (y : ℝ) :
    g.F y = ∑ j, g.weight j * ∫ s in -g.K..g.K,
      Real.cos (g.angularFrequency j * s) * Real.cos ((2 * Real.pi * y) * s) := by
  unfold F
  simp_rw [polynomial_eq_sum, Finset.sum_mul, mul_assoc]
  rw [intervalIntegral.integral_finset_sum]
  · simp_rw [intervalIntegral.integral_const_mul]
  · intro j _
    apply Continuous.intervalIntegrable (μ := volume)
    fun_prop

private theorem sin_frequency_add (g : CosineTest) (j : Fin g.modes) (t : ℝ) :
    Real.sin ((g.angularFrequency j + t) * g.K) = (-1 : ℝ) ^ j.val * Real.cos (t * g.K) := by
  rw [add_mul, angularFrequency_mul_K,
    show Real.pi / 2 + (j.val : ℝ) * Real.pi + t * g.K =
      (t * g.K + Real.pi / 2) + (j.val : ℝ) * Real.pi by ring,
    Real.sin_add_nat_mul_pi, Real.sin_add_pi_div_two]

private theorem sin_frequency_sub (g : CosineTest) (j : Fin g.modes) (t : ℝ) :
    Real.sin ((g.angularFrequency j - t) * g.K) = (-1 : ℝ) ^ j.val * Real.cos (t * g.K) := by
  simpa only [← sub_eq_add_neg, neg_mul, Real.cos_neg] using g.sin_frequency_add j (-t)

private theorem integral_cos_product_closed (g : CosineTest) (j : Fin g.modes) (y : ℝ)
    (hn : (frequency j : ℝ) ^ 2 ≠ (4 * g.K * y) ^ 2) :
    (∫ s in -g.K..g.K, Real.cos (g.angularFrequency j * s) * Real.cos (2 * Real.pi * y * s)) =
      4 * g.K / Real.pi * Real.cos (2 * Real.pi * g.K * y) *
        ((-1 : ℝ) ^ j.val * frequency j / ((frequency j : ℝ) ^ 2 - (4 * g.K * y) ^ 2)) := by
  let a := g.angularFrequency j
  let b := 2 * Real.pi * y
  have hscale : a ^ 2 - b ^ 2 = (Real.pi / (2 * g.K)) ^ 2 *
      ((frequency j : ℝ) ^ 2 - (4 * g.K * y) ^ 2) := by
    dsimp [a, b, angularFrequency]
    field_simp [g.K_pos.ne']
    ring
  have hdenom : a ^ 2 - b ^ 2 ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero (pow_ne_zero _ (div_ne_zero Real.pi_ne_zero
      (mul_ne_zero (by norm_num) g.K_pos.ne'))) (sub_ne_zero.mpr hn)
  have hdiff : a - b ≠ 0 := by
    intro heq
    exact hdenom (by rw [sub_eq_zero.mp heq, sub_self])
  have hsum : a + b ≠ 0 := by
    intro heq
    have hab : a = -b := eq_neg_of_add_eq_zero_left heq
    exact hdenom (by rw [hab]; ring)
  change (∫ s in -g.K..g.K, Real.cos (a * s) * Real.cos (b * s)) = _
  rw [integral_cos_product, integral_scaled_cos _ _ hdiff, integral_scaled_cos _ _ hsum]
  change (2 * Real.sin ((g.angularFrequency j - b) * g.K) / (a - b) +
    2 * Real.sin ((g.angularFrequency j + b) * g.K) / (a + b)) / 2 = _
  rw [sin_frequency_sub, sin_frequency_add]
  have hcos : 2 * Real.pi * g.K * y = b * g.K := by dsimp [b]; ring
  rw [hcos]
  calc
    _ = 2 * a * ((-1 : ℝ) ^ j.val * Real.cos (b * g.K)) / (a ^ 2 - b ^ 2) := by
      field_simp [hdiff, hsum, hdenom]
      ring
    _ = _ := by
      rw [hscale]
      dsimp [a, angularFrequency]
      field_simp [g.K_pos.ne', Real.pi_ne_zero, sub_ne_zero.mpr hn]
      ring

/-- The real Fourier transform away from the removable singularities. -/
theorem F_eq_closed_form (g : CosineTest) (y : ℝ)
    (hn : ∀ j : Fin g.modes, (frequency j : ℝ) ^ 2 ≠ (4 * g.K * y) ^ 2) :
    g.F y = 4 * g.K / Real.pi * Real.cos (2 * Real.pi * g.K * y) *
      ∑ j : Fin g.modes,
        (-1 : ℝ) ^ j.val * frequency j * g.weight j /
          ((frequency j : ℝ) ^ 2 - (4 * g.K * y) ^ 2) := by
  rw [F_eq_sum_integrals, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [g.integral_cos_product_closed j y (hn j)]
  ring

private theorem integral_cos_angular_product (g : CosineTest) (i j : Fin g.modes) :
    (∫ s in -g.K..g.K, Real.cos (g.angularFrequency j * s) *
      Real.cos (g.angularFrequency i * s)) = if j = i then g.K else 0 := by
  have hsum_eq : (g.angularFrequency j + g.angularFrequency i) * g.K =
      ((j.val + i.val + 1 : ℕ) : ℝ) * Real.pi := by
    rw [add_mul, angularFrequency_mul_K, angularFrequency_mul_K]
    push_cast
    ring
  have hsum_ne : g.angularFrequency j + g.angularFrequency i ≠ 0 := by
    intro heq
    rw [heq, zero_mul] at hsum_eq
    exact (show 0 < ((j.val + i.val + 1 : ℕ) : ℝ) * Real.pi by positivity).ne' hsum_eq.symm
  have hintsum : (∫ s in -g.K..g.K, Real.cos ((g.angularFrequency j + g.angularFrequency i) * s)) =
      0 := by
    rw [integral_scaled_cos _ _ hsum_ne, hsum_eq, Real.sin_nat_mul_pi, mul_zero, zero_div]
  rw [integral_cos_product, hintsum]
  by_cases hij : j = i
  · subst j
    rw [if_pos rfl]
    simp only [sub_self, zero_mul, Real.cos_zero, intervalIntegral.integral_const, smul_eq_mul]
    ring
  · rw [if_neg hij]
    have hdiff_eq : (g.angularFrequency j - g.angularFrequency i) * g.K =
        ((j.val : ℤ) - (i.val : ℤ) : ℤ) * Real.pi := by
      rw [sub_mul, angularFrequency_mul_K, angularFrequency_mul_K]
      push_cast
      ring
    have hdiff_ne : g.angularFrequency j - g.angularFrequency i ≠ 0 := by
      intro heq
      rw [heq, zero_mul] at hdiff_eq
      have habs : (((j.val : ℤ) - (i.val : ℤ) : ℤ) : ℝ) = 0 :=
        (mul_eq_zero.mp hdiff_eq.symm).resolve_right Real.pi_ne_zero
      apply hij
      apply Fin.ext
      exact_mod_cast (sub_eq_zero.mp (show (j.val : ℤ) - (i.val : ℤ) = 0 by exact_mod_cast habs))
    rw [integral_scaled_cos _ _ hdiff_ne, hdiff_eq, Real.sin_int_mul_pi]
    ring

/-- Value at each of the positive removable singularities. -/
theorem F_angular_value (g : CosineTest) (i : Fin g.modes) :
    g.F ((frequency i : ℝ) / (4 * g.K)) = g.K * g.weight i := by
  rw [F_eq_sum_integrals]
  have heq : 2 * Real.pi * ((frequency i : ℝ) / (4 * g.K)) = g.angularFrequency i := by
    unfold angularFrequency
    ring
  rw [heq]
  simp_rw [integral_cos_angular_product, mul_ite, mul_zero]
  simp [mul_comm]

private theorem hasDerivAt_compact_integral {𝕜 : Type*} [RCLike 𝕜] [ProperSpace 𝕜]
    {f f' : 𝕜 → ℝ → 𝕜} {a b : ℝ} (hab : a ≤ b)
    (hf : Continuous (fun p : 𝕜 × ℝ ↦ f p.1 p.2))
    (hf' : Continuous (fun p : 𝕜 × ℝ ↦ f' p.1 p.2))
    (hd : ∀ y s, HasDerivAt (fun t ↦ f t s) (f' y s) y) (y : 𝕜) :
    HasDerivAt (fun z ↦ ∫ s in a..b, f z s) (∫ s in a..b, f' y s) y := by
  let K := Metric.closedBall y 1
  let μ := volume.restrict (Ioc a b)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hK' : K ∈ 𝓝 y := Metric.closedBall_mem_nhds _ zero_lt_one
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_Icc : IsCompact (Icc a b))).bddAbove_image
    hf'.norm.continuousOn
  have hBound : ∀ᵐ s ∂μ, ∀ z ∈ K, ‖f' z s‖ ≤ C := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := a) (b := b))] with s hs
    exact fun z hz ↦ hC ⟨(z, s), ⟨hz, Ioc_subset_Icc_self hs⟩, rfl⟩
  have hInt (z : 𝕜) : Integrable (f z) μ := by
    have hcont : Continuous (f z) := hf.comp
      (continuous_const.prodMk continuous_id : Continuous (fun s : ℝ ↦ (z, s)))
    exact (hcont.intervalIntegrable a b).1
  have hMeas' : AEStronglyMeasurable (f' y) μ := by
    have hcont : Continuous (f' y) := hf'.comp
      (continuous_const.prodMk continuous_id : Continuous (fun s : ℝ ↦ (y, s)))
    exact hcont.aestronglyMeasurable
  have hCInt : Integrable (fun _ : ℝ ↦ C) μ :=
    (intervalIntegrable_const (c := C) (μ := volume) (a := a) (b := b)).1
  simp_rw [intervalIntegral.integral_of_le hab]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hK'
    (Eventually.of_forall fun z ↦ (hInt z).aestronglyMeasurable) (hInt y) hMeas' hBound hCInt
    (Eventually.of_forall fun s z _ ↦ hd z s)).2

private theorem hasDerivAt_cos_linear (c y : ℝ) :
    HasDerivAt (fun z ↦ Real.cos (c * z)) (-Real.sin (c * y) * c) y := by
  simpa only [id_eq, mul_one] using
    (Real.hasDerivAt_cos (c * y)).comp y ((hasDerivAt_id y).const_mul c)

private theorem hasDerivAt_sin_linear (c y : ℝ) :
    HasDerivAt (fun z ↦ Real.sin (c * z)) (Real.cos (c * y) * c) y := by
  simpa only [id_eq, mul_one] using
    (Real.hasDerivAt_sin (c * y)).comp y ((hasDerivAt_id y).const_mul c)

theorem hasDerivAt_F (g : CosineTest) (y : ℝ) :
    HasDerivAt g.F (∫ s in -g.K..g.K,
      g.polynomial s * (-Real.sin ((2 * Real.pi * s) * y) * (2 * Real.pi * s))) y := by
  have hfun : g.F = fun z ↦ ∫ s in -g.K..g.K, g.polynomial s * Real.cos ((2 * Real.pi * s) * z) := by
    ext z
    unfold F
    congr 1
    funext s
    rw [show 2 * Real.pi * z * s = 2 * Real.pi * s * z by ring]
  rw [hfun]
  exact hasDerivAt_compact_integral g.neg_K_le_K (by fun_prop) (by fun_prop)
    (fun z s ↦ (hasDerivAt_cos_linear _ z).const_mul (g.polynomial s)) y

theorem deriv_F (g : CosineTest) (y : ℝ) :
    deriv g.F y = ∫ s in -g.K..g.K,
      g.polynomial s * (-Real.sin ((2 * Real.pi * s) * y) * (2 * Real.pi * s)) :=
  (g.hasDerivAt_F y).deriv

theorem hasDerivAt_deriv_F (g : CosineTest) (y : ℝ) :
    HasDerivAt (deriv g.F) (∫ s in -g.K..g.K,
      g.polynomial s * (-Real.cos ((2 * Real.pi * s) * y) * (2 * Real.pi * s) ^ 2)) y := by
  rw [show deriv g.F = _ from funext g.deriv_F]
  refine hasDerivAt_compact_integral
    (f := fun z s ↦ g.polynomial s * (-Real.sin ((2 * Real.pi * s) * z) * (2 * Real.pi * s)))
    (f' := fun z s ↦ g.polynomial s * (-Real.cos ((2 * Real.pi * s) * z) * (2 * Real.pi * s) ^ 2))
    g.neg_K_le_K (by fun_prop) (by fun_prop) (fun z s ↦ ?_) y
  have h := (((hasDerivAt_sin_linear (2 * Real.pi * s) z).neg).mul_const
    (2 * Real.pi * s)).const_mul (g.polynomial s)
  exact h.congr_deriv (by ring)

theorem F_contDiff_one (g : CosineTest) : ContDiff ℝ 1 g.F :=
  contDiff_one_iff_deriv.mpr ⟨fun y ↦ (g.hasDerivAt_F y).differentiableAt,
    (show Differentiable ℝ (deriv g.F) from fun y ↦
      (g.hasDerivAt_deriv_F y).differentiableAt).continuous⟩

theorem F_contDiff_two (g : CosineTest) : ContDiff ℝ 2 g.F := by
  have hC : Continuous (deriv (deriv g.F)) := by
    let f (y s : ℝ) := g.polynomial s * (-Real.cos ((2 * Real.pi * s) * y) * (2 * Real.pi * s) ^ 2)
    have h : deriv (deriv g.F) = fun y ↦ ∫ s in Icc (-g.K) g.K, f y s := by
      ext y
      rw [(g.hasDerivAt_deriv_F y).deriv, intervalIntegral.integral_of_le g.neg_K_le_K,
        integral_Icc_eq_integral_Ioc]
    rw [h]
    exact continuous_parametric_integral_of_continuous (by show Continuous f.uncurry; unfold f; fun_prop)
      isCompact_Icc
  have hd₁ : Differentiable ℝ g.F := fun y ↦ (g.hasDerivAt_F y).differentiableAt
  have hd₂ : Differentiable ℝ (deriv g.F) := fun y ↦ (g.hasDerivAt_deriv_F y).differentiableAt
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  exact ⟨hd₁, by simp, contDiff_one_iff_deriv.mpr ⟨hd₂, hC⟩⟩

theorem differentiable_complexF (g : CosineTest) : Differentiable ℂ g.complexF := by
  intro y
  have hfun : g.complexF = fun z ↦ ∫ s in -g.K..g.K,
      (g.polynomial s : ℂ) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (s : ℂ)) * z) := by
    ext z
    unfold complexF
    congr 1
    funext s
    rw [mul_right_comm]
  rw [hfun]
  refine (hasDerivAt_compact_integral (f' := fun z s ↦ (g.polynomial s : ℂ) *
    (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (s : ℂ)) * z) *
      (2 * (Real.pi : ℂ) * Complex.I * (s : ℂ))))
    g.neg_K_le_K (by fun_prop) (by fun_prop) (fun z s ↦ ?_) y).differentiableAt
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (s : ℂ)
  simpa only [id_eq, mul_one, c] using
    ((Complex.hasDerivAt_exp (c * z)).comp z ((hasDerivAt_id z).const_mul c)).const_mul
      (g.polynomial s : ℂ)

private theorem integral_sine_product_eq_zero (g : CosineTest) (y : ℝ) :
    (∫ s in -g.K..g.K, g.polynomial s * Real.sin (2 * Real.pi * y * s)) = 0 := by
  let f := fun s : ℝ ↦ g.polynomial s * Real.sin (2 * Real.pi * y * s)
  have hf (s : ℝ) : f (-s) = -f s := by simp [f, g.polynomial_even s]
  have heq := intervalIntegral.integral_comp_neg (a := -g.K) (b := g.K) f
  rw [neg_neg] at heq
  simp_rw [hf, intervalIntegral.integral_neg] at heq
  change (∫ s in -g.K..g.K, f s) = 0
  linarith

theorem complexF_ofReal (g : CosineTest) (y : ℝ) : g.complexF y = (g.F y : ℂ) := by
  let f := fun s : ℝ ↦ (g.polynomial s : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ) * (s : ℂ))
  have hfun (s : ℝ) : f s =
        ((g.polynomial s * Real.cos (2 * Real.pi * y * s) : ℝ) : ℂ) +
          ((g.polynomial s * Real.sin (2 * Real.pi * y * s) : ℝ) : ℂ) * Complex.I := by
    dsimp [f]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (y : ℂ) * (s : ℂ) =
        ((2 * Real.pi * y * s : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
    simp only [Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_sin]
    ring
  have hcont : Continuous f := by dsimp [f]; fun_prop
  have hf := (hcont.intervalIntegrable (μ := volume) (-g.K) g.K).1
  have hre (s : ℝ) : RCLike.re (f s) = g.polynomial s * Real.cos (2 * Real.pi * y * s) := by
    change (f s).re = _
    rw [hfun]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have him (s : ℝ) : RCLike.im (f s) = g.polynomial s * Real.sin (2 * Real.pi * y * s) := by
    change (f s).im = _
    rw [hfun]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
  change (∫ s in -g.K..g.K, f s) = (g.F y : ℂ)
  rw [intervalIntegral.integral_of_le g.neg_K_le_K]
  apply Complex.ext
  · calc
      _ = ∫ s in Ioc (-g.K) g.K, RCLike.re (f s) := (integral_re hf).symm
      _ = _ := by simp only [hre, Complex.ofReal_re, F, intervalIntegral.integral_of_le g.neg_K_le_K]
  · calc
      _ = ∫ s in Ioc (-g.K) g.K, RCLike.im (f s) := (integral_im hf).symm
      _ = _ := by
        simp only [him, Complex.ofReal_im, ← intervalIntegral.integral_of_le g.neg_K_le_K]
        exact g.integral_sine_product_eq_zero y

private theorem integral_abs_symmetric (g : CosineTest) :
    (∫ s in -g.K..g.K, |s|) = g.K ^ 2 := by
  have hInt : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ ↦ |s|) volume a b :=
    continuous_abs.intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals (hInt (-g.K) 0) (hInt 0 g.K)]
  have h₁ : (∫ s in -g.K..0, |s|) = ∫ s in -g.K..0, -s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (by linarith [g.K_pos] : -g.K ≤ 0)] at hs
    exact abs_of_nonpos hs.2
  have h₂ : (∫ s in 0..g.K, |s|) = ∫ s in 0..g.K, s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le g.K_pos.le] at hs
    exact abs_of_nonneg hs.1
  rw [h₁, h₂, intervalIntegral.integral_neg, integral_id, integral_id]
  ring

theorem abs_deriv_F_le (g : CosineTest) (y : ℝ) :
    |deriv g.F y| ≤ 2 * Real.pi * g.K ^ 2 * g.weightSum := by
  rw [g.deriv_F]
  apply (intervalIntegral.abs_integral_le_integral_abs g.neg_K_le_K).trans
  calc
    (∫ s in -g.K..g.K, |g.polynomial s * (-Real.sin ((2 * Real.pi * s) * y) *
        (2 * Real.pi * s))|) ≤ ∫ s in -g.K..g.K, (2 * Real.pi * g.weightSum) * |s| := by
      apply intervalIntegral.integral_mono_on g.neg_K_le_K
        ((show Continuous _ by fun_prop).intervalIntegrable _ _)
        ((show Continuous _ by fun_prop).intervalIntegrable _ _)
      intro s _
      simp only [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * Real.pi)]
      have hmul : |g.polynomial s| * |Real.sin ((2 * Real.pi * s) * y)| ≤ g.weightSum :=
        (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)).trans
          (g.abs_polynomial_le_weightSum s)
      calc
        _ = (2 * Real.pi) * (|g.polynomial s| * |Real.sin ((2 * Real.pi * s) * y)|) * |s| := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmul (by positivity)) (abs_nonneg _)
    _ = _ := by rw [intervalIntegral.integral_const_mul, g.integral_abs_symmetric]; ring

theorem abs_deriv_deriv_F_le (g : CosineTest) (y : ℝ) :
    |deriv (deriv g.F) y| ≤ (2 * Real.pi) ^ 2 * (2 * g.K ^ 3 / 3) * g.weightSum := by
  rw [(g.hasDerivAt_deriv_F y).deriv]
  apply (intervalIntegral.abs_integral_le_integral_abs g.neg_K_le_K).trans
  calc
    (∫ s in -g.K..g.K, |g.polynomial s * (-Real.cos ((2 * Real.pi * s) * y) *
        (2 * Real.pi * s) ^ 2)|) ≤ ∫ s in -g.K..g.K, ((2 * Real.pi) ^ 2 * g.weightSum) * s ^ 2 := by
      apply intervalIntegral.integral_mono_on g.neg_K_le_K
        ((show Continuous _ by fun_prop).intervalIntegrable _ _)
        ((show Continuous _ by fun_prop).intervalIntegrable _ _)
      intro s _
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (2 * Real.pi * s))]
      have hmul : |g.polynomial s| * |Real.cos ((2 * Real.pi * s) * y)| ≤ g.weightSum :=
        (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)).trans
          (g.abs_polynomial_le_weightSum s)
      calc
        _ = (2 * Real.pi) ^ 2 * (|g.polynomial s| * |Real.cos ((2 * Real.pi * s) * y)|) * s ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmul (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_pow]; norm_num; ring

end Legendre.CosineTest

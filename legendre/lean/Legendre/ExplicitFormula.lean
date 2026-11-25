import Legendre.CosineTail
import Legendre.Geometry
import Legendre.ZeroSum
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.AbelSummation

namespace Legendre

open Complex Filter MeasureTheory Set
open scoped BigOperators Interval Topology

private theorem measurable_psiZero : Measurable psiZero := by
  unfold psiZero
  have hfloor : Measurable (fun x : ℝ ↦ (⌊x⌋₊ : ℝ)) :=
    (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp Nat.measurable_floor
  apply Chebyshev.psi_mono.measurable.sub
  apply Measurable.ite (measurableSet_eq_fun hfloor measurable_id) _ measurable_const
  exact (measurable_of_countable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n / 2)).comp
    Nat.measurable_floor

private theorem aestronglyMeasurable_explicitFormulaError (a b T : ℝ) (ha : 2 ≤ a) :
    AEStronglyMeasurable (fun x ↦ explicitFormulaError x T) (volume.restrict (Icc a b)) := by
  classical
  rw [show (fun x ↦ explicitFormulaError x T) =
    fun x ↦ (psiZero x : ℂ) - ((x : ℂ) -
        (∑ ρ ∈ (zerosIn (-T) T).filter (fun ρ ↦ |ρ.im| < T),
          (zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)) - (Real.log (2 * Real.pi) : ℂ) -
        (Real.log (1 - x⁻¹ ^ 2) / 2 : ℝ)) from rfl]
  have hψ := (continuous_ofReal.measurable.comp measurable_psiZero).aestronglyMeasurable
    (μ := volume.restrict (Icc a b))
  have hlog : Measurable (fun x : ℝ ↦ ((Real.log (1 - x⁻¹ ^ 2) / 2 : ℝ) : ℂ)) :=
    continuous_ofReal.measurable.comp
      ((Real.measurable_log.comp (measurable_const.sub (measurable_id.inv.pow_const 2))).div_const 2)
  refine hψ.sub (((continuous_ofReal.measurable.aestronglyMeasurable.sub ?_).sub
    aestronglyMeasurable_const).sub hlog.aestronglyMeasurable)
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Icc
  apply continuousOn_finset_sum _
  intro ρ _
  refine continuousOn_const.mul ((continuousOn_of_forall_continuousAt ?_).div_const ρ)
  intro x hx
  exact continuousAt_ofReal_cpow_const x ρ (Or.inr (by linarith [hx.1]))

private theorem primePowerDistance_pos_of_not_nat {x : ℝ}
    (hx : x ∉ range (fun n : ℕ ↦ (n : ℝ))) : 0 < primePowerDistance x := by
  have hclosed := Nat.isClosedEmbedding_coe_real.isClosed_range
  have hpos := (hclosed.notMem_iff_infDist_pos ⟨(2 : ℝ), by exact ⟨2, by norm_num⟩⟩).mp hx
  have hnonempty : {y : ℝ | ∃ n : ℕ, IsPrimePow n ∧ y = n ∧ y ≠ x}.Nonempty := by
    refine ⟨2, 2, Nat.prime_two.isPrimePow, by norm_num, ?_⟩
    rintro rfl
    exact hx ⟨2, by norm_num⟩
  exact hpos.trans_le (Metric.infDist_le_infDist_of_subset (fun _ ⟨n, _, heq, _⟩ ↦
    ⟨n, heq.symm⟩) hnonempty)

private theorem tendsto_log_sq_div_top (b : ℝ) (hb : 0 < b) :
    Tendsto (fun T : ℝ ↦ b * Real.log (b * T) ^ 2 / T) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
    (tendsto_id.const_mul_atTop hb)
  have h' := h.const_mul (b ^ 2)
  simp only [mul_zero, Function.comp_apply, id_eq, one_mul, add_zero] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  field_simp [hb.ne', hT.ne']

private theorem tendsto_explicitFormulaError (h : CitedFacts) (x : ℝ) (hx : 2 ≤ x)
    (hd : 0 < primePowerDistance x) : Tendsto (explicitFormulaError x) atTop (𝓝 0) := by
  obtain ⟨C, hC, hrem⟩ := h.explicitFormula
  have hdiv := ((tendsto_id.atTop_mul_const hd).inv_tendsto_atTop).const_mul x
  have hdiv' : Tendsto (fun T : ℝ ↦ x / (T * primePowerDistance x)) atTop (𝓝 0) := by
    simpa only [Pi.inv_apply, div_eq_mul_inv, mul_zero] using hdiv
  have hmin := tendsto_const_nhds (x := (1 : ℝ)) |>.min hdiv'
  rw [min_eq_right zero_le_one] at hmin
  have hlog : Tendsto (fun T : ℝ ↦ Real.log x * min 1 (x / (T * primePowerDistance x))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hmin.const_mul (Real.log x)
  have hupper := ((tendsto_log_sq_div_top x (by linarith)).add hlog).const_mul C
  rw [add_zero, mul_zero] at hupper
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    ((eventually_ge_atTop (2 : ℝ)).mono fun T hT ↦ hrem x T hx hT) hupper

/-- The Davenport remainder tends to zero when integrated against any integrable weight on a
fixed compact interval above `2`. -/
theorem tendsto_integral_explicitFormulaError_mul (h : CitedFacts) (a b : ℝ) (ha : 2 ≤ a)
    (hab : a ≤ b) (g : ℝ → ℂ) (hg : IntegrableOn g (Icc a b)) :
    Tendsto (fun T : ℝ ↦ ∫ x in Icc a b, explicitFormulaError x T * g x) atTop (𝓝 0) := by
  obtain ⟨C, hC, hrem⟩ := h.explicitFormula
  have hbl : 2 ≤ b := ha.trans hab
  have hb : 0 < b := by linarith
  have hexistsUpper := (tendsto_order.mp (tendsto_log_sq_div_top b hb)).2 1 zero_lt_one
  have hlimit : ∀ᵐ x ∂volume.restrict (Icc a b),
      Tendsto (fun T : ℝ ↦ explicitFormulaError x T * g x) atTop (𝓝 (0 : ℂ)) := by
    have hn : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ range (fun n : ℕ ↦ (n : ℝ)) :=
      compl_mem_ae_iff.mpr ((countable_range _).measure_zero _)
    filter_upwards [hn.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem (μ := volume) (measurableSet_Icc (a := a) (b := b))] with x hx hxab
    simpa only [zero_mul] using (tendsto_explicitFormulaError h x (ha.trans hxab.1)
      (primePowerDistance_pos_of_not_nat hx)).mul_const (g x)
  have hmeas : ∀ T, AEStronglyMeasurable (fun x ↦ explicitFormulaError x T * g x)
      (volume.restrict (Icc a b)) := fun T ↦
    (aestronglyMeasurable_explicitFormulaError a b T ha).mul hg.aestronglyMeasurable
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ᵐ x ∂volume.restrict (Icc a b),
      ‖explicitFormulaError x T * g x‖ ≤ C * (1 + Real.log b) * ‖g x‖ := by
    filter_upwards [eventually_ge_atTop (2 : ℝ), hexistsUpper] with T hT hTD
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc (a := a) (b := b))] with x hx
    have hx2 : 2 ≤ x := ha.trans hx.1
    have hx_pos : 0 < x := by linarith
    have hT_pos : 0 < T := by linarith
    have hprod : 1 ≤ x * T := by nlinarith
    have hlog₀ : 0 ≤ Real.log (x * T) := Real.log_nonneg hprod
    have hlog₁ : Real.log (x * T) ≤ Real.log (b * T) :=
      Real.log_le_log (mul_pos hx_pos hT_pos) (mul_le_mul_of_nonneg_right hx.2 hT_pos.le)
    have hsq := pow_le_pow_left₀ hlog₀ hlog₁ 2
    have hfirst : x * Real.log (x * T) ^ 2 / T ≤ b * Real.log (b * T) ^ 2 / T :=
      div_le_div_of_nonneg_right (mul_le_mul hx.2 hsq (sq_nonneg _) hb.le) hT_pos.le
    have hsecond : Real.log x * min 1 (x / (T * primePowerDistance x)) ≤ Real.log b := by
      calc
        _ ≤ Real.log x * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.log_nonneg (by linarith))
        _ ≤ _ := by simpa only [mul_one] using Real.log_le_log hx_pos hx.2
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (hrem x T hx2 hT).trans (mul_le_mul_of_nonneg_left
      (add_le_add (hfirst.trans hTD.le) hsecond) hC)
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ C * (1 + Real.log b) * ‖g x‖) (Eventually.of_forall hmeas) hbound
      (hg.norm.const_mul _) hlimit
  rwa [integral_zero] at hlim

private theorem ae_psiZero_eq_psi : psiZero =ᵐ[volume] Chebyshev.psi := by
  have hn : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ range (fun n : ℕ ↦ (n : ℝ)) :=
    compl_mem_ae_iff.mpr ((countable_range _).measure_zero _)
  filter_upwards [hn] with x hx
  have he : (⌊x⌋₊ : ℝ) ≠ x := fun he ↦ hx ⟨⌊x⌋₊, he⟩
  simp [psiZero, he]

private theorem psi_eq_Icc_sum (x : ℝ) :
    Chebyshev.psi x = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  simp [Chebyshev.psi]

private theorem abel_vonMangoldt {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (f : ℝ → ℝ)
    (hdf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hf' : IntegrableOn (deriv f) (Icc a b)) (hfa : f a = 0) (hfb : f b = 0) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * ArithmeticFunction.vonMangoldt n) =
      -(∫ t in Ioc a b, deriv f t * psiZero t) := by
  have h := sum_mul_eq_sub_sub_integral_mul (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n)
    (f := f) ha hab hdf hf'
  simp_rw [← psi_eq_Icc_sum, hfa, hfb, zero_mul, sub_zero, zero_sub] at h
  rw [h]
  congr 1
  apply setIntegral_congr_ae measurableSet_Ioc
  filter_upwards [ae_psiZero_eq_psi] with t ht _
  rw [ht]

private theorem integral_pairing_by_parts {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hdf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hf' : ContinuousOn (deriv f) (Icc a b)) (hfa : f a = 0) (hfb : f b = 0)
    {U U' : ℝ → ℂ} (hU : ∀ t ∈ Icc a b, HasDerivAt U (U' t) t)
    (hU' : ContinuousOn U' (Icc a b)) :
    (∫ t in Ioc a b, U t * ((deriv f t : ℝ) : ℂ)) = -(∫ t in Ioc a b, U' t * (f t : ℂ)) := by
  have hfc (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun x : ℝ ↦ (f x : ℂ)) ((deriv f t : ℝ) : ℂ) t := (hdf t ht).hasDerivAt.ofReal_comp
  have hfi : ContinuousOn (fun t ↦ ((deriv f t : ℝ) : ℂ)) (Icc a b) :=
    continuous_ofReal.comp_continuousOn hf'
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (by rwa [uIcc_of_le hab]) (by rwa [uIcc_of_le hab])
    (hU'.intervalIntegrable_of_Icc hab) (hfi.intervalIntegrable_of_Icc hab)
  simpa only [intervalIntegral.integral_of_le hab, hfa, hfb, ofReal_zero, mul_zero, sub_zero,
    zero_sub] using hi

private noncomputable def mellinOn (a b : ℝ) (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioc a b, (t : ℂ) ^ (s - 1) * (f t : ℂ)

private noncomputable def trivialDensity (t : ℝ) : ℝ := 1 / (t * (t ^ 2 - 1))

private theorem hasDerivAt_log_correction {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun x : ℝ ↦ Real.log (1 - x⁻¹ ^ 2) / 2) (trivialDensity t) t := by
  have ht₀ := zero_lt_one.trans ht
  have hInv : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
  have hsq : t⁻¹ ^ 2 < 1 := by
    simpa only [one_pow] using pow_lt_pow_left₀ hInv (inv_nonneg.mpr ht₀.le) (by decide : (2 : ℕ) ≠ 0)
  have hinner := ((hasDerivAt_inv ht₀.ne').pow 2).const_sub 1
  have hd := (Real.hasDerivAt_log (sub_ne_zero.mpr hsq.ne')).comp t hinner
  convert hd.div_const 2 using 1
  unfold trivialDensity
  push_cast
  have hn : t ^ 2 - 1 ≠ 0 := by nlinarith only [ht, mul_pos (sub_pos.mpr ht) (show 0 < t + 1 by positivity)]
  field_simp [ht₀.ne', hn]

private theorem continuousOn_trivialDensity (a b : ℝ) (ha : 2 ≤ a) :
    ContinuousOn trivialDensity (Icc a b) := by
  unfold trivialDensity
  apply continuousOn_const.div (by fun_prop)
  intro t ht
  have ht' : 1 < t := lt_of_lt_of_le (by norm_num) (ha.trans ht.1)
  exact mul_ne_zero (by linarith) (by
    nlinarith only [ht', mul_pos (sub_pos.mpr ht') (show 0 < t + 1 by positivity)])

private theorem correction_by_parts {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) {f : ℝ → ℝ}
    (hdf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hf' : ContinuousOn (deriv f) (Icc a b)) (hfa : f a = 0) (hfb : f b = 0) :
    (∫ t in Ioc a b, (Real.log (1 - t⁻¹ ^ 2) / 2 : ℝ) * ((deriv f t : ℝ) : ℂ)) =
      -(∫ t in Ioc a b, (trivialDensity t : ℂ) * (f t : ℂ)) := by
  apply integral_pairing_by_parts hab hdf hf' hfa hfb
  · intro t ht
    exact (hasDerivAt_log_correction (lt_of_lt_of_le (by norm_num) (ha.trans ht.1))).ofReal_comp
  · exact continuous_ofReal.comp_continuousOn (continuousOn_trivialDensity a b ha)

private theorem zero_term_by_parts {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) {f : ℝ → ℝ}
    (hdf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hf' : ContinuousOn (deriv f) (Icc a b)) (hfa : f a = 0) (hfb : f b = 0)
    {ρ : ℂ} (hρ : ρ ≠ 0) :
    (∫ t in Ioc a b, ((t : ℂ) ^ ρ / ρ) * ((deriv f t : ℝ) : ℂ)) = -mellinOn a b f ρ := by
  apply integral_pairing_by_parts hab hdf hf' hfa hfb
  · intro t ht
    have ht₀ : t ≠ 0 := by linarith [ha.trans ht.1]
    have hd := (hasDerivAt_ofReal_cpow_const ht₀ hρ).div_const ρ
    convert hd using 1
    rw [mul_comm, mul_div_cancel_right₀ _ hρ]
  · apply continuousOn_of_forall_continuousAt
    intro t ht
    exact continuousAt_ofReal_cpow_const t _ (Or.inr (by linarith [ha.trans ht.1]))

private noncomputable def truncatedZeros (T : ℝ) : Finset ℂ := by
  classical
  exact (zerosIn (-T) T).filter (fun ρ ↦ |ρ.im| < T)

private theorem mem_truncatedZeros {T : ℝ} {ρ : ℂ} :
    ρ ∈ truncatedZeros T ↔ ρ ∈ nontrivialZeros ∧ |ρ.im| < T := by
  classical
  simp only [truncatedZeros, Finset.mem_filter, mem_zerosIn]
  constructor
  · rintro ⟨⟨hρ, _, _⟩, hT⟩
    exact ⟨hρ, hT⟩
  · rintro ⟨hρ, hT⟩
    obtain ⟨hl, hu⟩ := abs_lt.mp hT
    exact ⟨⟨hρ, hl.le, hu.le⟩, hT⟩

private theorem finite_mellin_identity {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) {f : ℝ → ℝ}
    (hdf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hf' : ContinuousOn (deriv f) (Icc a b)) (hfa : f a = 0) (hfb : f b = 0) (T : ℝ) :
    ((∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) +
      (∑ ρ ∈ truncatedZeros T, (zeroMultiplicity ρ : ℂ) * mellinOn a b f ρ) +
      (∫ t in Ioc a b, (trivialDensity t : ℂ) * (f t : ℂ)) +
      (∫ t in Ioc a b, explicitFormulaError t T * ((deriv f t : ℝ) : ℂ)) =
      mellinOn a b f 1 := by
  let d (t : ℝ) : ℂ := (deriv f t : ℝ)
  let P (t : ℝ) : ℂ := (psiZero t : ℂ) * d t
  let X (t : ℝ) : ℂ := (t : ℂ) * d t
  let Z (ρ : ℂ) (t : ℝ) : ℂ := (zeroMultiplicity ρ : ℂ) * (((t : ℂ) ^ ρ / ρ) * d t)
  let C (t : ℝ) : ℂ := (Real.log (2 * Real.pi) : ℂ) * d t
  let L (t : ℝ) : ℂ := (Real.log (1 - t⁻¹ ^ 2) / 2 : ℝ) * d t
  have hd : ContinuousOn d (Icc a b) := continuous_ofReal.comp_continuousOn hf'
  have integrable (v : ℝ → ℂ) (hv : ContinuousOn v (Icc a b)) :
      IntegrableOn v (Ioc a b) := (hv.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hP : IntegrableOn P (Ioc a b) := by
    have hPc : AEStronglyMeasurable P (volume.restrict (Ioc a b)) :=
      ((continuous_ofReal.measurable.comp measurable_psiZero).aestronglyMeasurable).mul
        (integrable d hd).aestronglyMeasurable
    apply ((integrable d hd).norm.const_mul (Chebyshev.psi b)).mono' hPc
    filter_upwards [ae_psiZero_eq_psi.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := a) (b := b))] with t ht ht'
    dsimp only [P]
    rw [ht, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (Chebyshev.psi_nonneg t)]
    exact mul_le_mul_of_nonneg_right (Chebyshev.psi_mono ht'.2) (norm_nonneg _)
  have hX := integrable X (continuous_ofReal.continuousOn.mul hd)
  have hZ (ρ : ℂ) : IntegrableOn (Z ρ) (Ioc a b) := by
    apply integrable
    refine continuousOn_const.mul ((?_ : ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ ρ) (Icc a b)).div_const ρ |>.mul hd)
    exact continuousOn_of_forall_continuousAt fun t ht ↦
      continuousAt_ofReal_cpow_const t ρ (Or.inr (by linarith [ha.trans ht.1]))
  have hC := integrable C (continuousOn_const.mul hd)
  have hL := integrable L ((continuous_ofReal.comp_continuousOn
    (continuousOn_of_forall_continuousAt fun t ht ↦
      (hasDerivAt_log_correction (lt_of_lt_of_le (by norm_num) (ha.trans ht.1))).continuousAt)).mul hd)
  have hZS : IntegrableOn (fun t ↦ ∑ ρ ∈ truncatedZeros T, Z ρ t) (Ioc a b) :=
    integrable_finset_sum _ fun ρ _ ↦ hZ ρ
  have hseparate : (∫ t in Ioc a b, explicitFormulaError t T * d t) =
      (∫ t in Ioc a b, P t) - (∫ t in Ioc a b, X t) +
      (∑ ρ ∈ truncatedZeros T, ∫ t in Ioc a b, Z ρ t) +
      (∫ t in Ioc a b, C t) + ∫ t in Ioc a b, L t := by
    calc
      _ = ∫ t in Ioc a b, (P t - X t + (∑ ρ ∈ truncatedZeros T, Z ρ t) + C t) + L t := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t _
        change (psiZero t - ((t : ℂ) - (∑ ρ ∈ truncatedZeros T,
          (zeroMultiplicity ρ : ℂ) * ((t : ℂ) ^ ρ / ρ)) - (Real.log (2 * Real.pi) : ℂ) -
          (Real.log (1 - t⁻¹ ^ 2) / 2 : ℝ))) * d t = _
        dsimp only [P, X, Z, C, L]
        simp only [sub_mul, Finset.sum_mul, mul_assoc]
        abel
      _ = _ := by
        rw [integral_add (f := fun t ↦ P t - X t + (∑ ρ ∈ truncatedZeros T, Z ρ t) + C t)
          (((hP.sub hX).add hZS).add hC) hL,
          integral_add (f := fun t ↦ P t - X t + ∑ ρ ∈ truncatedZeros T, Z ρ t)
            ((hP.sub hX).add hZS) hC,
          integral_add (f := fun t ↦ P t - X t) (hP.sub hX) hZS,
          integral_sub hP hX, integral_finset_sum _ (fun ρ _ ↦ hZ ρ)]
  have hPI : (∫ t in Ioc a b, P t) =
      -((∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) := by
    have h := abel_vonMangoldt (by linarith) hab f hdf hf'.integrableOn_Icc hfa hfb
    simp only [P, d, ← ofReal_mul, integral_complex_ofReal]
    rw [h, ofReal_neg, neg_neg]
    simp only [mul_comm (psiZero _)]
  have hXI : (∫ t in Ioc a b, X t) = -mellinOn a b f 1 := by
    have hx := integral_pairing_by_parts hab hdf hf' hfa hfb
      (U := Complex.ofReal) (U' := fun _ ↦ 1)
      (fun t _ ↦ by simpa using (hasDerivAt_id t).ofReal_comp) continuousOn_const
    simpa only [X, d, mellinOn, sub_self, cpow_zero] using hx
  have hCI : (∫ t in Ioc a b, C t) = 0 := by
    have hc := integral_pairing_by_parts hab hdf hf' hfa hfb
      (U := fun _ ↦ Real.log (2 * Real.pi)) (U' := fun _ ↦ 0)
      (fun t _ ↦ hasDerivAt_const t _) continuousOn_const
    simpa only [C, d, zero_mul, integral_zero, neg_zero] using hc
  have hLI := correction_by_parts ha hab hdf hf' hfa hfb
  have hZI : (∑ ρ ∈ truncatedZeros T, ∫ t in Ioc a b, Z ρ t) =
      -(∑ ρ ∈ truncatedZeros T, (zeroMultiplicity ρ : ℂ) * mellinOn a b f ρ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hρ₀ : ρ ≠ 0 := fun he ↦ by
      have hpos := (mem_truncatedZeros.mp hρ).1.1
      rw [he, zero_re] at hpos
      exact (lt_irrefl 0 hpos)
    calc
      _ = (zeroMultiplicity ρ : ℂ) *
          (∫ t in Ioc a b, ((t : ℂ) ^ ρ / ρ) * ((deriv f t : ℝ) : ℂ)) :=
        integral_const_mul (zeroMultiplicity ρ : ℂ) _
      _ = _ := by rw [zero_term_by_parts ha hab hdf hf' hfa hfb hρ₀, mul_neg]
  change _ + (∫ t in Ioc a b, explicitFormulaError t T * d t) = _
  rw [hseparate, hPI, hXI, hZI, hCI]
  rw [show (∫ t in Ioc a b, L t) = _ from hLI]
  abel

private noncomputable def truncatedZerosSubtype (T : ℝ) : Finset nontrivialZeros := by
  classical
  exact (truncatedZeros T).subtype (fun ρ ↦ ρ ∈ nontrivialZeros)

private theorem tendsto_truncatedZerosSubtype :
    Tendsto truncatedZerosSubtype atTop atTop := by
  classical
  apply tendsto_atTop.2
  intro S
  have hl : ∀ᶠ T : ℝ in atTop, ∀ ρ ∈ S, |(ρ : ℂ).im| < T :=
    (eventually_all_finset S).mpr fun ρ _ ↦ eventually_gt_atTop |(ρ : ℂ).im|
  filter_upwards [hl] with T hT ρ hρ
  exact Finset.mem_subtype.mpr (mem_truncatedZeros.mpr ⟨ρ.property, hT ρ hρ⟩)

private theorem tendsto_truncatedZeros_sum (m : ℂ → ℂ)
    (hm : Summable (fun ρ : nontrivialZeros ↦ m ρ)) :
    Tendsto (fun T ↦ ∑ ρ ∈ truncatedZeros T, m ρ) atTop (𝓝 (∑' ρ : nontrivialZeros, m ρ)) := by
  classical
  have ht := hm.hasSum.comp tendsto_truncatedZerosSubtype
  refine ht.congr fun T ↦ ?_
  change (∑ ρ ∈ (truncatedZeros T).subtype (fun ρ ↦ ρ ∈ nontrivialZeros), m ρ) = _
  rw [Finset.sum_subtype_eq_sum_filter m, Finset.filter_true_of_mem]
  exact fun _ hρ ↦ (mem_truncatedZeros.mp hρ).1

/-- The compactly supported Mellin identity obtained from Davenport's truncated formula. -/
theorem compact_mellin_identity (h : CitedFacts) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    {f : ℝ → ℝ} (hdf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hf' : ContinuousOn (deriv f) (Icc a b)) (hfa : f a = 0) (hfb : f b = 0)
    (hsum : Summable (fun ρ : nontrivialZeros ↦ (zeroMultiplicity ρ : ℂ) * mellinOn a b f ρ)) :
    ((∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) +
      (∑' ρ : nontrivialZeros, (zeroMultiplicity ρ : ℂ) * mellinOn a b f ρ) +
      (∫ t in Ioc a b, (trivialDensity t : ℂ) * (f t : ℂ)) =
      mellinOn a b f 1 := by
  have hi : IntegrableOn (fun t ↦ ((deriv f t : ℝ) : ℂ)) (Icc a b) :=
    (continuous_ofReal.comp_continuousOn hf').integrableOn_Icc
  have he := tendsto_integral_explicitFormulaError_mul h a b ha hab _ hi
  simp_rw [integral_Icc_eq_integral_Ioc] at he
  have hz := tendsto_truncatedZeros_sum (fun ρ ↦ (zeroMultiplicity ρ : ℂ) * mellinOn a b f ρ) hsum
  let P : ℂ := ((∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
  let L : ℂ := ∫ t in Ioc a b, (trivialDensity t : ℂ) * (f t : ℂ)
  have ht := (((tendsto_const_nhds (x := P)).add hz).add (tendsto_const_nhds (x := L))).add he
  simp only [add_zero] at ht
  exact tendsto_nhds_unique ht
    (tendsto_const_nhds.congr (fun T ↦ (finite_mellin_identity ha hab hdf hf' hfa hfb T).symm))

private noncomputable def windowTest (w : Window) (g : CosineTest) (t : ℝ) : ℝ :=
  (Real.sqrt t)⁻¹ * g.polynomial (w.scale t)

private theorem windowTest_contDiffOn (w : Window) (g : CosineTest) (ha : 0 < w.a) :
    ContDiffOn ℝ 1 (windowTest w g) (Ioi 0) := by
  have hs : ContDiffOn ℝ 1 w.scale (Ioi 0) := by
    unfold Window.scale
    apply ContDiffOn.div_const
    apply (contDiff_id.contDiffOn.div_const w.a).log
    exact fun t ht ↦ (div_pos ht ha).ne'
  have hroot : ContDiffOn ℝ 1 Real.sqrt (Ioi 0) :=
    contDiffOn_id.sqrt fun _ ht ↦ (mem_Ioi.mp ht).ne'
  exact (hroot.inv fun _ ht ↦ (Real.sqrt_pos.mpr ht).ne').mul
    ((g.contDiff_polynomial.of_le (by norm_num)).comp_contDiffOn hs)

private theorem sum_windowTest_eq_primePowerSum (w : Window) (g : CosineTest)
    (ha : 0 < w.a) (hD : 0 < w.D) (hleft : 2 ≤ w.endpoint (-g.K)) :
    (∑ n ∈ Finset.Ioc ⌊w.endpoint (-g.K)⌋₊ ⌊w.endpoint g.K⌋₊,
      windowTest w g n * ArithmeticFunction.vonMangoldt n) = primePowerSum w g := by
  classical
  let A := w.endpoint (-g.K)
  let B := w.endpoint g.K
  have hA : 0 ≤ A := by linarith
  have hAB : A ≤ B := (w.endpoint_strictMono ha hD).monotone (by linarith [g.K_pos])
  have hB := hA.trans hAB
  unfold primePowerSum
  calc
    _ = ∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊,
        ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) * g.G (w.scale n) := by
      apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hn
      have hl' : A < (n : ℝ) := (Nat.floor_lt hA).mp hl
      have hu' : (n : ℝ) ≤ B := (Nat.le_floor_iff hB).mp hu
      have hn₀ : 0 < (n : ℝ) := hA.trans_lt hl'
      have hs : w.scale n ∈ Icc (-g.K) g.K := by
        have hmono := w.endpoint_strictMono ha hD
        exact ⟨hmono.le_iff_le.mp (by rw [w.endpoint_scale ha hD hn₀]; exact hl'.le),
          hmono.le_iff_le.mp (by rw [w.endpoint_scale ha hD hn₀]; exact hu')⟩
      rw [g.G_eq_polynomial hs, windowTest, div_eq_mul_inv]
      ring
    _ = _ := by
      apply Finset.sum_subset
      · intro n hn
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Finset.mem_Ioc.mp hn).2)
      · intro n hn hn'
        have hna : n ≤ ⌊A⌋₊ := le_of_not_gt fun hl ↦ hn' (Finset.mem_Ioc.mpr
          ⟨hl, Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)⟩)
        have hna' : (n : ℝ) ≤ A := (Nat.le_floor_iff hA).mp hna
        rcases Nat.eq_zero_or_pos n with rfl | hn₀
        · simp
        · have hn₀' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn₀
          have hs : w.scale n ≤ -g.K := (w.endpoint_strictMono ha hD).le_iff_le.mp
            (by rwa [w.endpoint_scale ha hD hn₀'])
          rcases lt_or_eq_of_le hs with hs | hs
          · rw [g.G_eq_zero (fun hm ↦ (not_le_of_gt hs) hm.1), mul_zero]
          · rw [hs, g.G_endpoints.1, mul_zero]

private theorem mellin_density_mul {t : ℝ} (ht : 0 < t) (z : ℂ) :
    (t : ℂ) * (t : ℂ) ^ (z - 1) * (Real.sqrt t : ℂ)⁻¹ =
      Complex.exp ((z - 1 / 2) * (Real.log t : ℂ)) := by
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hex : (t : ℂ) = Complex.exp (Real.log t : ℂ) := by
    rw [← ofReal_exp, Real.exp_log ht]
  rw [cpow_def_of_ne_zero ht', ← ofReal_log ht.le, ← ofReal_inv, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos ht, ← Real.exp_neg, ofReal_exp, hex]
  push_cast
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

private theorem mellin_windowTest (w : Window) (g : CosineTest) (ha : 0 < w.a) (hD : 0 < w.D)
    (z : ℂ) :
    mellinOn (w.endpoint (-g.K)) (w.endpoint g.K) (windowTest w g) z =
      ((w.D : ℂ) * Complex.exp ((z - 1 / 2) * (Real.log w.a : ℂ))) *
        (∫ s in -g.K..g.K, (g.polynomial s : ℂ) *
          Complex.exp ((z - 1 / 2) * (w.D : ℂ) * (s : ℂ))) := by
  have hK : -g.K ≤ g.K := by linarith [g.K_pos]
  have hAB := (w.endpoint_strictMono ha hD).monotone hK
  let H (t : ℝ) : ℂ := (t : ℂ) ^ (z - 1) * (windowTest w g t : ℂ)
  have hH : ContinuousOn H (w.endpoint '' [[-g.K, g.K]]) := by
    have hs : w.endpoint '' [[-g.K, g.K]] ⊆ Ioi 0 := by
      rintro _ ⟨s, _, rfl⟩
      exact w.endpoint_pos ha s
    apply ContinuousOn.mono _ hs
    apply ContinuousOn.mul
    · apply continuousOn_of_forall_continuousAt
      intro t ht
      exact continuousAt_ofReal_cpow_const t _ (Or.inr (mem_Ioi.mp ht).ne')
    · exact continuous_ofReal.comp_continuousOn (windowTest_contDiffOn w g ha).continuousOn
  have hderiv (s : ℝ) : HasDerivAt w.endpoint (w.D * w.endpoint s) s := by
    have h := ((hasDerivAt_id s).const_mul w.D).exp.const_mul w.a
    convert h using 1
    simp [Window.endpoint, mul_left_comm, mul_comm]
  have hs := intervalIntegral.integral_deriv_smul_comp' (fun s _ ↦ hderiv s)
    (by unfold Window.endpoint; fun_prop) hH
  unfold mellinOn
  rw [← intervalIntegral.integral_of_le hAB]
  change (∫ t in w.endpoint (-g.K)..w.endpoint g.K, H t) = _
  rw [← hs]
  refine Eq.trans ?_ (intervalIntegral.integral_const_mul _ _)
  apply intervalIntegral.integral_congr
  intro s _
  let t := w.endpoint s
  have ht : 0 < t := w.endpoint_pos ha s
  have hlog : Real.log t = Real.log w.a + w.D * s := by
    unfold t Window.endpoint
    rw [Real.log_mul ha.ne' (Real.exp_pos _).ne', Real.log_exp]
  change (w.D * t) • ((t : ℂ) ^ (z - 1) * (windowTest w g t : ℂ)) = _
  rw [Complex.real_smul]
  unfold windowTest
  rw [w.scale_endpoint ha hD]
  push_cast
  rw [show (w.D : ℂ) * (t : ℂ) * ((t : ℂ) ^ (z - 1) *
      ((Real.sqrt t : ℂ)⁻¹ * (g.polynomial s : ℂ))) =
    (w.D : ℂ) * (g.polynomial s : ℂ) *
      ((t : ℂ) * (t : ℂ) ^ (z - 1) * (Real.sqrt t : ℂ)⁻¹) by ring,
    mellin_density_mul ht, hlog]
  push_cast
  rw [mul_add, ← mul_assoc (z - 1 / 2), Complex.exp_add]
  ring

private theorem mellin_windowTest_real (w : Window) (g : CosineTest)
    (ha : 0 < w.a) (hD : 0 < w.D) (r : ℝ) :
    mellinOn (w.endpoint (-g.K)) (w.endpoint g.K) (windowTest w g) r =
      ((w.D * w.a ^ (r - 1 / 2) *
        ∫ s in -g.K..g.K, g.polynomial s * Real.exp ((r - 1 / 2) * w.D * s) : ℝ) : ℂ) := by
  rw [mellin_windowTest w g ha hD, Real.rpow_def_of_pos ha]
  push_cast
  rw [mul_comm (Real.log w.a : ℂ)]
  congr 1
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro s _
  push_cast
  rfl

private theorem mellin_windowTest_pole (w : Window) (g : CosineTest)
    (ha : 0 < w.a) (hD : 0 < w.D) :
    mellinOn (w.endpoint (-g.K)) (w.endpoint g.K) (windowTest w g) 1 = (poleTerm w g : ℂ) := by
  have hreflect :
      (∫ s in -g.K..g.K, g.polynomial s * Real.exp (-(w.D * s / 2))) =
        ∫ s in -g.K..g.K, g.polynomial s * Real.exp (w.D * s / 2) := by
    have hh := intervalIntegral.integral_comp_neg (a := -g.K) (b := g.K)
      (f := fun s ↦ g.polynomial s * Real.exp (w.D * s / 2))
    have heven (s : ℝ) : g.polynomial (-s) = g.polynomial s := g.polynomial_even s
    simpa only [neg_neg, heven, mul_neg, neg_div] using hh
  have hcosh :
      (∫ s in -g.K..g.K, g.polynomial s * Real.cosh (w.D * s / 2)) =
        ∫ s in -g.K..g.K, g.polynomial s * Real.exp (w.D * s / 2) := by
    calc
      _ = ∫ s in -g.K..g.K, (g.polynomial s * Real.exp (w.D * s / 2) +
          g.polynomial s * Real.exp (-(w.D * s / 2))) / 2 := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp only
        rw [Real.cosh_eq]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _), hreflect]
        ring
  rw [← ofReal_one, mellin_windowTest_real w g ha hD, poleTerm, Window.P, hcosh,
    Real.sqrt_eq_rpow]
  simp only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    show ∀ s : ℝ, 1 / 2 * w.D * s = w.D * s / 2 by intro s; ring]

private theorem mellin_windowTest_zero (hRH : RiemannHypothesis) (w : Window) (g : CosineTest)
    (ha : 0 < w.a) (hD : 0 < w.D) (ρ : nontrivialZeros) :
    mellinOn (w.endpoint (-g.K)) (w.endpoint g.K) (windowTest w g) ρ =
      (w.D : ℂ) * Complex.exp ((((ρ : ℂ).im * Real.log w.a : ℝ) : ℂ) * I) *
        (g.F (w.Δ * (ρ : ℂ).im) : ℂ) := by
  have hz : (ρ : ℂ) - 1 / 2 = ((ρ : ℂ).im : ℂ) * I := by
    apply Complex.ext <;> simp [sub_re, sub_im,
      nontrivialZero_re_of_RH hRH ρ.property]
  have hi : (∫ s in -g.K..g.K, (g.polynomial s : ℂ) *
      Complex.exp (((ρ : ℂ).im : ℂ) * I * (w.D : ℂ) * (s : ℂ))) =
      g.complexF (w.Δ * (ρ : ℂ).im : ℝ) := by
    unfold CosineTest.complexF
    apply intervalIntegral.integral_congr
    intro s _
    unfold Window.Δ
    push_cast
    congr 2
    field_simp [Real.pi_ne_zero]
  rw [mellin_windowTest w g ha hD, hz, hi, g.complexF_ofReal]
  push_cast
  congr 3
  ring

private theorem summable_mellin_windowTest (hRH : RiemannHypothesis) (w : Window) (g : CosineTest)
    (ha : 0 < w.a) (hD : 0 < w.D) (hnorm : Summable (weightedZeroNorm g.F w.D)) :
    Summable (fun ρ : nontrivialZeros ↦ (zeroMultiplicity ρ : ℂ) *
      mellinOn (w.endpoint (-g.K)) (w.endpoint g.K) (windowTest w g) ρ) := by
  apply (hnorm.mul_left w.D).of_norm_bounded
  intro ρ
  rw [mellin_windowTest_zero hRH w g ha hD ρ]
  simp only [norm_mul, norm_natCast, norm_real, Real.norm_eq_abs, abs_of_pos hD,
    norm_exp_ofReal_mul_I, mul_one, weightedZeroNorm, Window.Δ]
  ring_nf
  exact le_rfl

private theorem re_mellin_windowTest_zero (hRH : RiemannHypothesis) (w : Window) (g : CosineTest)
    (ha : 0 < w.a) (hD : 0 < w.D) (ρ : nontrivialZeros) :
    ((zeroMultiplicity ρ : ℂ) *
      mellinOn (w.endpoint (-g.K)) (w.endpoint g.K) (windowTest w g) ρ).re =
      w.D * weightedZeroTerm w g ρ := by
  rw [mellin_windowTest_zero hRH w g ha hD ρ]
  simp only [weightedZeroTerm, mul_re, mul_im, exp_re, ofReal_re, ofReal_im,
    I_re, I_im, natCast_re, natCast_im, mul_zero, zero_mul, mul_one, zero_add, add_zero, sub_zero,
    Real.exp_zero, one_mul]
  ring_nf

private theorem hasSum_mellin_trivialZeros {a b : ℝ} (ha : 2 ≤ a) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    HasSum (fun k : ℕ ↦ mellinOn a b f (-(2 * ((k : ℂ) + 1))))
      (∫ t in Ioc a b, (trivialDensity t : ℂ) * (f t : ℂ)) := by
  let F (k : ℕ) (t : ℝ) : ℂ := ((t⁻¹ ^ 3 * (t⁻¹ ^ 2) ^ k : ℝ) : ℂ) * (f t : ℂ)
  have hEq (k : ℕ) :
      mellinOn a b f (-(2 * ((k : ℂ) + 1))) = ∫ t in Ioc a b, F k t := by
    unfold mellinOn
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    dsimp only
    rw [show -(2 * ((k : ℂ) + 1)) - 1 = -((3 + 2 * k : ℕ) : ℂ) by push_cast; ring,
      cpow_neg, cpow_natCast, ← inv_pow, pow_add, pow_mul]
    simp only [F, ofReal_mul, ofReal_pow, ofReal_inv, mul_comm]
  simp_rw [hEq]
  let bd (k : ℕ) (t : ℝ) : ℝ := (1 / 4 : ℝ) ^ k * ‖f t‖
  have hgeom := hasSum_geometric_of_norm_lt_one (ξ := (1 / 4 : ℝ)) (by norm_num)
  have hgood : ∀ᵐ t ∂volume.restrict (Ioc a b), t ∈ Ioc a b := ae_restrict_mem measurableSet_Ioc
  apply hasSum_integral_of_dominated_convergence bd
  · intro k
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    have hInv : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Ioc a b) :=
      continuousOn_id.inv₀ fun t ht ↦ (show 0 < t by linarith [ht.1]).ne'
    exact (continuous_ofReal.comp_continuousOn ((hInv.pow 3).mul ((hInv.pow 2).pow k))).mul
      (continuous_ofReal.comp_continuousOn (hf.mono Ioc_subset_Icc_self))
  · intro k
    filter_upwards [hgood] with t ht
    have ht₂ : 2 ≤ t := ha.trans ht.1.le
    have ht₀ : 0 < t := by linarith
    have hinv : t⁻¹ ≤ 1 / 2 := (inv_anti₀ (by norm_num) ht₂).trans_eq (by norm_num)
    have hinv₀ := inv_nonneg.mpr ht₀.le
    have h2 : t⁻¹ ^ 2 ≤ 1 / 4 := (pow_le_pow_left₀ hinv₀ hinv 2).trans_eq (by norm_num)
    have h3 : t⁻¹ ^ 3 ≤ 1 := (pow_le_pow_left₀ hinv₀ hinv 3).trans (by norm_num)
    dsimp only [F]
    rw [norm_mul, norm_real, norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ t⁻¹ ^ 3 * (t⁻¹ ^ 2) ^ k)]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul h3 (pow_le_pow_left₀ (sq_nonneg t⁻¹) h2 k) (by positivity) zero_le_one).trans_eq
        (one_mul _)) (norm_nonneg _)
  · exact Eventually.of_forall fun t ↦ (hgeom.mul_right ‖f t‖).summable
  · have he (t : ℝ) : (∑' k, bd k t) = (1 - (1 / 4 : ℝ))⁻¹ * ‖f t‖ :=
      (hgeom.mul_right ‖f t‖).tsum_eq
    simp_rw [he]
    exact ((hf.integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self).norm.const_mul _
  · filter_upwards [hgood] with t ht
    have ht₂ : 2 ≤ t := ha.trans ht.1.le
    have ht₀ : 0 < t := by linarith
    have hinv : t⁻¹ ≤ 1 / 2 := (inv_anti₀ (by norm_num) ht₂).trans_eq (by norm_num)
    have h2 : t⁻¹ ^ 2 ≤ 1 / 4 :=
      (pow_le_pow_left₀ (inv_nonneg.mpr ht₀.le) hinv 2).trans_eq (by norm_num)
    have hgeom' := hasSum_geometric_of_norm_lt_one (ξ := t⁻¹ ^ 2)
      (by simpa only [Real.norm_of_nonneg (sq_nonneg _)] using h2.trans_lt (by norm_num))
    have hcast := Complex.ofRealCLM.hasSum ((hgeom'.mul_left (t⁻¹ ^ 3)).mul_right (f t))
    have hrat : t⁻¹ ^ 3 * (1 - t⁻¹ ^ 2)⁻¹ = trivialDensity t := by
      have hne : t ^ 2 - 1 ≠ 0 := by nlinarith [mul_nonneg (show 0 ≤ t - 2 by linarith) ht₀.le]
      have hne' : 1 - t⁻¹ ^ 2 ≠ 0 := by linarith
      unfold trivialDensity
      field_simp [ht₀.ne', hne, hne']
    simpa only [F, ofRealCLM_apply, ofReal_mul, hrat] using hcast

/-- Lemma 14 on windows with lower support at least two. -/
theorem smoothed_explicit_formula (hRH : RiemannHypothesis) (h : CitedFacts)
    (g : CosineTest) (w : Window) (hD : 0 < w.D) (hA : 2 ≤ w.endpoint (-g.K)) :
    Summable (weightedZeroNorm g.F w.D) ∧ Summable (trivialZeroTerm w g) ∧
    primePowerSum w g + w.D * (∑' ρ : nontrivialZeros, weightedZeroTerm w g ρ) +
      w.D * (∑' k, trivialZeroTerm w g k) = poleTerm w g := by
  let A := w.endpoint (-g.K)
  let B := w.endpoint g.K
  let f := windowTest w g
  have ha : 0 < w.a := by
    have hapos : 0 < A := by linarith
    exact pos_of_mul_pos_left hapos (Real.exp_pos _).le
  have hAB : A ≤ B := (w.endpoint_strictMono ha hD).monotone (by linarith [g.K_pos])
  have hsub : Icc A B ⊆ Ioi (0 : ℝ) := fun t ht ↦ by
    have hAt := hA.trans ht.1
    exact mem_Ioi.mpr (by linarith)
  have hfc := windowTest_contDiffOn w g ha
  have hdf : ∀ t ∈ Icc A B, DifferentiableAt ℝ f t := fun t ht ↦
    (hfc.differentiableOn_one t (hsub ht)).differentiableAt (isOpen_Ioi.mem_nhds (hsub ht))
  have hf' : ContinuousOn (deriv f) (Icc A B) :=
    (hfc.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hfa : f A = 0 := by
    simp only [f, A, windowTest, w.scale_endpoint ha hD, g.polynomial_neg_endpoint, mul_zero]
  have hfb : f B = 0 := by
    simp only [f, B, windowTest, w.scale_endpoint ha hD, g.polynomial_pos_endpoint, mul_zero]
  have hnorm := weightedZeroNorm_summable hRH h g.F g.F_even g.F_contDiff_one g.F_decay
    g.derivative_integration_bounds.1 g.derivative_integration_bounds.2 g.mass g.abs_F_le_mass w.D hD
  have hmsum := summable_mellin_windowTest hRH w g ha hD hnorm
  have hid := compact_mellin_identity h hA hAB hdf hf' hfa hfb hmsum
  rw [sum_windowTest_eq_primePowerSum w g ha hD hA, mellin_windowTest_pole w g ha hD] at hid
  have hZ : (∑' ρ : nontrivialZeros, (zeroMultiplicity ρ : ℂ) * mellinOn A B f ρ).re =
      w.D * (∑' ρ : nontrivialZeros, weightedZeroTerm w g ρ) := by
    change Complex.reCLM _ = _
    rw [Complex.reCLM.map_tsum hmsum, ← tsum_mul_left]
    exact tsum_congr (re_mellin_windowTest_zero hRH w g ha hD)
  let L : ℂ := ∫ t in Ioc A B, (trivialDensity t : ℂ) * (f t : ℂ)
  have hL : HasSum (fun k : ℕ ↦ w.D * trivialZeroTerm w g k) L.re := by
    have hl := Complex.reCLM.hasSum (hasSum_mellin_trivialZeros hA (hfc.continuousOn.mono hsub))
    have he (k : ℕ) :
        Complex.reCLM (mellinOn A B f (-(2 * ((k : ℂ) + 1)))) = w.D * trivialZeroTerm w g k := by
      have hk := mellin_windowTest_real w g ha hD (-(2 * ((k : ℝ) + 1)))
      push_cast at hk
      change (mellinOn A B f (-(2 * ((k : ℂ) + 1)))).re = w.D * trivialZeroTerm w g k
      rw [hk]
      simp only [← ofReal_mul, ofReal_re]
      unfold trivialZeroTerm
      rw [show -(2 * ((k : ℝ) + 1)) - 1 / 2 = -(2 * ((k : ℝ) + 1) + 1 / 2) by ring]
      ring
    change HasSum (fun k : ℕ ↦ Complex.reCLM (mellinOn A B f (-(2 * ((k : ℂ) + 1))))) L.re at hl
    simpa only [he] using hl
  have ht : Summable (trivialZeroTerm w g) := (summable_mul_left_iff hD.ne').mp hL.summable
  refine ⟨hnorm, ht, ?_⟩
  change _ + _ + L = _ at hid
  have hr := congrArg Complex.re hid
  simp only [add_re, ofReal_re] at hr
  rw [hZ, ← hL.tsum_eq, tsum_mul_left] at hr
  exact hr

end Legendre

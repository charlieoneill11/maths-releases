import Chowla.CountingShells
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace Chowla

open Filter MeasureTheory Set
open scoped BigOperators Topology

private noncomputable def prefixSet (P : ℕ → Prop) [DecidablePred P] (X : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊X⌋₊).filter P

private theorem prefix_mono (P : ℕ → Prop) [DecidablePred P] : Monotone (prefixSet P) := by
  intro X Y hXY n hn
  simp only [prefixSet, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans (Nat.floor_mono hXY)⟩, hn.2⟩

private theorem prefix_card_le (P : ℕ → Prop) [DecidablePred P] {X : ℝ} (hX : 0 ≤ X) :
    ((prefixSet P X).card : ℝ) ≤ X := by
  have hc := Finset.card_filter_le (s := Finset.Icc 1 ⌊X⌋₊) (p := P)
  simp only [Nat.card_Icc, add_tsub_cancel_right] at hc
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le hX)

private theorem ShellWeight.deriv_continuous (W : ShellWeight) : Continuous (deriv W.toFun) :=
  W.smooth.continuous_deriv (by norm_num)

private theorem ShellWeight.integral_eq_intervalIntegral (W : ShellWeight) :
    ∫ u : ℝ, W.toFun u = ∫ u in (1 : ℝ)..2, W.toFun u := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (1 : ℝ) 2) (f := W.toFun)
    fun u hu => W.zero_off_interval (fun h => hu ⟨h.1, h.2.le⟩)).symm

private theorem integral_ite_deriv (W : ShellWeight) {u : ℝ} (hu : u ≤ 2) :
    ∫ t in Ioc (1 : ℝ) 2, (if u ≤ t then deriv W.toFun t else 0) = -W.toFun u := by
  have hw₂ : W.toFun 2 = 0 := W.zero_off_interval (by simp)
  have hFTC (a : ℝ) (ha : a ≤ 2) : ∫ t in Icc a 2, deriv W.toFun t = -W.toFun a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha,
      intervalIntegral.integral_deriv_eq_sub (fun _ _ =>
        (W.smooth.differentiable (by norm_num)).differentiableAt)
        (W.deriv_continuous.intervalIntegrable _ _), hw₂, zero_sub]
  by_cases h : u ≤ 1
  · have hW : W.toFun u = 0 := W.zero_off_interval (fun ht => h.not_gt ht.1)
    rw [setIntegral_congr_fun measurableSet_Ioc (g := deriv W.toFun) (fun t ht => if_pos (h.trans ht.1.le)),
      ← integral_Icc_eq_integral_Ioc, hFTC 1 (by norm_num), W.zero_off_interval (show (1 : ℝ) ∉ Ioo 1 2 by simp), hW]
  · have heq : Ioc (1 : ℝ) 2 ∩ Ici u = Icc u 2 := by
      ext t
      exact ⟨fun ⟨ht, htu⟩ => ⟨htu, ht.2⟩, fun ht => ⟨⟨(lt_of_not_ge h).trans_le ht.1, ht.2⟩, ht.1⟩⟩
    change (∫ t in Ioc (1 : ℝ) 2, (Ici u).indicator (deriv W.toFun) t) = _
    rw [setIntegral_indicator measurableSet_Ici, heq, hFTC u hu]

private theorem sum_weights_eq_integral (W : ShellWeight) (P : ℕ → Prop) [DecidablePred P]
    {X : ℝ} (hX : 0 < X) :
    (∑ n ∈ prefixSet P (2 * X), W.toFun ((n : ℝ) / X)) / X =
      -(∫ t in Ioc (1 : ℝ) 2, (((prefixSet P (X * t)).card : ℝ) / X) * deriv W.toFun t) := by
  classical
  let S := prefixSet P (2 * X)
  let A := Ioc (1 : ℝ) 2
  let f (n : ℕ) (t : ℝ) := if (n : ℝ) / X ≤ t then deriv W.toFun t else 0
  have hint (n : ℕ) : IntegrableOn (f n) A := by
    change IntegrableOn ((Ici ((n : ℝ) / X)).indicator (deriv W.toFun)) A
    exact (W.deriv_continuous.integrableOn_Icc.mono_set Ioc_subset_Icc_self).indicator measurableSet_Ici
  have hsum (t : ℝ) (ht : t ∈ A) :
      ∑ n ∈ S, f n t = ((prefixSet P (X * t)).card : ℝ) * deriv W.toFun t := by
    have h₀ : 0 ≤ X * t := mul_nonneg hX.le (zero_le_one.trans ht.1.le)
    have hle : X * t ≤ 2 * X := by nlinarith only [mul_le_mul_of_nonneg_left ht.2 hX.le]
    have hf : S.filter (fun n : ℕ => (n : ℝ) / X ≤ t) = prefixSet P (X * t) := by
      ext n
      simp only [Finset.mem_filter]
      rw [div_le_iff₀ hX, mul_comm t X, ← Nat.le_floor_iff h₀]
      refine ⟨fun ⟨hn, hcut⟩ => ?_, fun hn => ⟨prefix_mono P hle hn, ?_⟩⟩
      · simp only [S, prefixSet, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
        exact ⟨⟨hn.1.1, hcut⟩, hn.2⟩
      · exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    rw [← hf]
    simp only [f, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hftc (n : ℕ) (hn : n ∈ S) : ∫ t in A, f n t = -W.toFun ((n : ℝ) / X) := by
    have hc := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    have hbound := (Nat.le_floor_iff (by positivity : 0 ≤ 2 * X)).mp hc
    exact integral_ite_deriv W ((div_le_iff₀ hX).2 hbound)
  have hsum_int : (∫ t in A, ((prefixSet P (X * t)).card : ℝ) * deriv W.toFun t) =
      ∑ n ∈ S, -W.toFun ((n : ℝ) / X) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun t => ∑ n ∈ S, f n t)
      (fun t ht => (hsum t ht).symm), integral_finset_sum S (fun n _ => hint n)]
    exact Finset.sum_congr rfl hftc
  simp only [div_mul_eq_mul_div, integral_div, hsum_int, Finset.sum_neg_distrib, neg_div, neg_neg, S, A]

private theorem signed_integral_deriv (W : ShellWeight) (c : ℝ) :
    -(∫ t in Ioc (1 : ℝ) 2, (c * t) * deriv W.toFun t) = c * ∫ u : ℝ, W.toFun u := by
  have hw₁ : W.toFun 1 = 0 := W.zero_off_interval (by simp)
  have hw₂ : W.toFun 2 = 0 := W.zero_off_interval (by simp)
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := id) (v := W.toFun) (a := 1) (b := 2) (u' := fun _ => 1)
    (v' := deriv W.toFun) continuous_id.continuousOn W.smooth.continuous.continuousOn
    (fun t _ => hasDerivAt_id t)
    (fun _ _ => ((W.smooth.differentiable (by norm_num)).differentiableAt).hasDerivAt)
    (continuous_const.intervalIntegrable _ _) (W.deriv_continuous.intervalIntegrable _ _)
  rw [W.integral_eq_intervalIntegral]
  simp only [id_eq, hw₁, hw₂, mul_zero, sub_zero, one_mul, zero_sub] at hb
  simp_rw [mul_assoc]
  rw [integral_const_mul, ← intervalIntegral.integral_of_le (by norm_num), hb, mul_neg, neg_neg]

/-- Partial summation transfers a natural-number prefix asymptotic to every smooth shell. -/
theorem weightedSum_tendsto_of_prefix (W : ShellWeight) (P : ℕ → Prop) [DecidablePred P] (c : ℝ)
    (h : Tendsto (fun X : ℝ => (((Finset.Icc 1 ⌊X⌋₊).filter P).card : ℝ) / X) atTop (𝓝 c)) :
    Tendsto (fun X : ℝ => (∑ n ∈ (Finset.Icc 1 ⌊2*X⌋₊).filter P, W.toFun ((n : ℝ) / X)) / X) atTop
      (𝓝 (c * ∫ u : ℝ, W.toFun u)) := by
  let A := Ioc (1 : ℝ) 2
  let μ : Measure ℝ := volume.restrict A
  let F (X t : ℝ) := (((prefixSet P (X * t)).card : ℝ) / X) * deriv W.toFun t
  have hmeas : ∀ᶠ X : ℝ in atTop, AEStronglyMeasurable (F X) μ := Eventually.of_forall fun X => by
    have hmono : Monotone (fun x : ℝ => ((prefixSet P x).card : ℝ)) :=
      fun _ _ hxy => Nat.cast_le.mpr (Finset.card_mono (prefix_mono P hxy))
    exact (((hmono.measurable.comp (measurable_const.mul measurable_id)).div_const X).mul
      W.deriv_continuous.measurable).aestronglyMeasurable
  have htmem : ∀ᵐ t : ℝ ∂μ, t ∈ A := ae_restrict_mem measurableSet_Ioc
  have hbound : ∀ᶠ X : ℝ in atTop, ∀ᵐ t : ℝ ∂μ, ‖F X t‖ ≤ 2 * |deriv W.toFun t| := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    filter_upwards [htmem] with t ht
    have ht₀ : 0 ≤ t := zero_le_one.trans ht.1.le
    have hc := prefix_card_le P (mul_nonneg hX.le ht₀)
    have hle : ((prefixSet P (X * t)).card : ℝ) / X ≤ 2 :=
      (div_le_iff₀ hX).2 (hc.trans (by nlinarith only [mul_le_mul_of_nonneg_left ht.2 hX.le]))
    unfold F
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg (by positivity) hX.le)]
    exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
  have hint : Integrable (fun t => 2 * |deriv W.toFun t|) μ :=
    (W.deriv_continuous.abs.const_mul 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hlim : ∀ᵐ t : ℝ ∂μ, Tendsto (fun X => F X t) atTop (𝓝 ((c * t) * deriv W.toFun t)) := by
    filter_upwards [htmem] with t ht
    have ht₀ : 0 < t := zero_lt_one.trans ht.1
    have hc : Tendsto (fun X : ℝ => (((prefixSet P (X * t)).card : ℝ) / (X * t))) atTop (𝓝 c) :=
      h.comp (tendsto_id.atTop_mul_const ht₀)
    apply ((hc.mul_const t).mul_const (deriv W.toFun t)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    unfold F
    have hcancel (b : ℝ) : b / (X * t) * t = b / X := by
      field_simp
    rw [hcancel]
  have hconv := (tendsto_integral_filter_of_dominated_convergence (fun t => 2 * |deriv W.toFun t|)
    hmeas hbound hint hlim).neg
  rw [show -(∫ t, (c * t) * deriv W.toFun t ∂μ) = c * ∫ u : ℝ, W.toFun u from
    signed_integral_deriv W c] at hconv
  apply hconv.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  exact (sum_weights_eq_integral W P hX).symm

end Chowla

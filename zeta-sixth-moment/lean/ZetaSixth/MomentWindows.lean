import ZetaSixth.MomentBasics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Finite

namespace ZetaSixth

open Filter Function MeasureTheory Set
open scoped BigOperators Topology

private theorem smoothedMoment_le_annulus (Φ : Weight) {T : ℝ} (hT : 0 < T)
    (hΦ : ∀ t, Φ t ≤ 1) :
    smoothedMoment Φ T ≤ ∫ t in T..(2 * T), momentDensity t := by
  have hs : support (fun t => Φ (t / T) * momentDensity t) ⊆ Ioc T (2 * T) := by
    intro t ht
    have hquot : t / T ∈ Ioo (1 : ℝ) 2 := by
      by_contra hn
      exact ht (by simp [Φ.zero_of_notMem hn])
    exact ⟨by simpa using (lt_div_iff₀ hT).1 hquot.1, ((div_lt_iff₀ hT).1 hquot.2).le⟩
  rw [smoothedMoment, ← intervalIntegral.integral_eq_integral_of_support_subset hs]
  refine intervalIntegral.integral_mono_on (by linarith) (smoothIntegrable Φ T).intervalIntegrable
    (continuous_momentDensity.intervalIntegrable _ _) ?_
  intro t _
  simpa using mul_le_mul_of_nonneg_right (hΦ (t / T)) (momentDensity_nonnegative t)

private noncomputable def dyadic (n : ℕ) (T : ℝ) : ℝ := T / 2 ^ n

private theorem dyadic_partition (n : ℕ) (T : ℝ) :
    M6 T = (∫ t in (0 : ℝ)..dyadic n T, momentDensity t) +
      ∑ i ∈ Finset.range n, ∫ t in (dyadic (i + 1) T)..(2 * dyadic (i + 1) T), momentDensity t := by
  induction n with
  | zero => simp [M6, dyadic, momentDensity]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hdy : 2 * dyadic (n + 1) T = dyadic n T := by
        simp only [dyadic, pow_succ]
        field_simp
      rw [hdy, ← intervalIntegral.integral_add_adjacent_intervals
        (continuous_momentDensity.intervalIntegrable 0 (dyadic (n + 1) T))
        (continuous_momentDensity.intervalIntegrable (dyadic (n + 1) T) (dyadic n T))]
      ring

private theorem dyadic_partition_le (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∑ i ∈ Finset.range n, ∫ t in (dyadic (i + 1) T)..(2 * dyadic (i + 1) T),
      momentDensity t) ≤ M6 T := by
  rw [dyadic_partition n T]
  exact le_add_of_nonneg_left (intervalIntegral.integral_nonneg_of_forall
    (div_nonneg hT (by positivity)) momentDensity_nonnegative)

private theorem dyadic_fraction (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 : ℝ) / 2 ^ (i + 1)) = 1 - (1 : ℝ) / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ (2 : ℝ) n]
      field_simp
      all_goals ring

private theorem tendsto_dyadic_fraction :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (1 : ℝ) / 2 ^ (i + 1)) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => 1 - (1 : ℝ) / 2 ^ n) atTop (𝓝 1) := by
    simpa [one_div, inv_pow] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).const_sub 1
  exact h.congr fun n => (dyadic_fraction n).symm

private theorem tendsto_log_dyadic_ratio (n : ℕ) :
    Tendsto (fun T : ℝ => Real.log (dyadic n T) / Real.log T) atTop (𝓝 1) := by
  have h : Tendsto (fun T : ℝ => 1 - Real.log (2 ^ n) / Real.log T) atTop (𝓝 1) := by
    simpa using (Real.tendsto_log_atTop.const_div_atTop (Real.log (2 ^ n))).const_sub 1
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  rw [dyadic, Real.log_div (zero_lt_one.trans hT).ne' (by positivity), sub_div,
    div_self (Real.log_pos hT).ne']

private noncomputable def dyadicScaleFactor (i : ℕ) (T : ℝ) : ℝ :=
  (1 / 2 ^ (i + 1)) * (Real.log (dyadic (i + 1) T) / Real.log T) ^ 9

private theorem dyadicScaleFactor_eq (i : ℕ) {T : ℝ} (hT : 1 < T) :
    dyadicScaleFactor i T = momentScale (dyadic (i + 1) T) / momentScale T := by
  have hT₀ : T ≠ 0 := (zero_lt_one.trans hT).ne'
  have hL : Real.log T ≠ 0 := (Real.log_pos hT).ne'
  have hc : c3 ≠ 0 := c3_pos.ne'
  unfold dyadicScaleFactor momentScale
  rw [div_pow]
  unfold dyadic
  field_simp

theorem sharp_of_smooth {c d : ℝ} (hcd : c < d)
    (hsmooth : ∀ Φ : Weight, ∀ᶠ T in atTop,
      d * momentScale T * (∫ t, Φ t) ≤ smoothedMoment Φ T) :
    ∀ᶠ T in atTop, c * c3 * T * Real.log T ^ 9 ≤ M6 T := by
  by_cases hc : 0 ≤ c
  · have hd : 0 < d := hc.trans_lt hcd
    have hε : 0 < 1 - c / d := sub_pos.mpr ((div_lt_iff₀ hd).2 (by simpa using hcd))
    obtain ⟨ε, hε₀, hε₁⟩ := exists_between hε
    have hε' : ε < 1 := hε₁.trans_le (sub_le_self _ (div_nonneg hc hd.le))
    obtain ⟨Φ, hΦ, hΦI⟩ := Weight.exists_integral_gt hε₀ hε'
    let A := d * ∫ t, Φ t
    have hcA : c < A := by
      have hb : c / d < ∫ t, Φ t := by linarith
      convert (div_lt_iff₀ hd).1 hb using 1
      rw [mul_comm]
    have hL : Tendsto (fun n : ℕ => A * ∑ i ∈ Finset.range n, (1 : ℝ) / 2 ^ (i + 1))
        atTop (𝓝 A) := by simpa using tendsto_dyadic_fraction.const_mul A
    obtain ⟨n, hn⟩ := (hL.eventually_const_lt hcA).exists
    have hsum : Tendsto (fun T : ℝ => ∑ i ∈ Finset.range n, dyadicScaleFactor i T) atTop
        (𝓝 (∑ i ∈ Finset.range n, (1 : ℝ) / 2 ^ (i + 1))) := by
      apply tendsto_finset_sum
      intro i _
      change Tendsto (fun T : ℝ => (1 / 2 ^ (i + 1)) *
        (Real.log (dyadic (i + 1) T) / Real.log T) ^ 9) atTop
        (𝓝 ((1 : ℝ) / 2 ^ (i + 1)))
      simpa using
        ((tendsto_log_dyadic_ratio (i + 1)).pow 9).const_mul (1 / (2 : ℝ) ^ (i + 1))
    have hs : ∀ᶠ T in atTop, ∀ i ∈ Finset.range n,
        d * momentScale (dyadic (i + 1) T) * (∫ t, Φ t) ≤ smoothedMoment Φ (dyadic (i + 1) T) := by
      rw [eventually_all_finset]
      intro i _
      exact (tendsto_id.atTop_div_const (show (0 : ℝ) < 2 ^ (i + 1) by positivity)).eventually
        (hsmooth Φ)
    filter_upwards [eventually_gt_atTop (1 : ℝ), (hsum.const_mul A).eventually_const_lt hn, hs]
      with T hT hTl hsT
    have hS := momentScale_pos hT
    have hfinal : c ≤ M6 T / momentScale T := by
      calc
        c ≤ A * ∑ i ∈ Finset.range n, dyadicScaleFactor i T := hTl.le
        _ = ∑ i ∈ Finset.range n, A * dyadicScaleFactor i T := Finset.mul_sum ..
        _ ≤ ∑ i ∈ Finset.range n,
            (∫ t in (dyadic (i + 1) T)..(2 * dyadic (i + 1) T), momentDensity t) / momentScale T := by
          apply Finset.sum_le_sum
          intro i hi
          rw [dyadicScaleFactor_eq i hT]
          apply (le_div_iff₀ hS).2
          rw [mul_assoc, div_mul_cancel₀ _ hS.ne']
          calc
            A * momentScale (dyadic (i + 1) T) =
                d * momentScale (dyadic (i + 1) T) * (∫ t, Φ t) := by dsimp [A]; ring
            _ ≤ smoothedMoment Φ (dyadic (i + 1) T) := hsT i hi
            _ ≤ _ := smoothedMoment_le_annulus Φ
              (div_pos (zero_lt_one.trans hT) (by positivity)) hΦ
        _ ≤ _ := by
          rw [← Finset.sum_div]
          exact div_le_div_of_nonneg_right (dyadic_partition_le n (zero_lt_one.trans hT).le) hS.le
    simpa only [momentScale, mul_assoc] using (le_div_iff₀ hS).1 hfinal
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hM : 0 ≤ M6 T := intervalIntegral.integral_nonneg_of_forall
      (zero_lt_one.trans hT).le momentDensity_nonnegative
    simpa only [momentScale, mul_assoc] using
      (mul_nonpos_of_nonpos_of_nonneg (not_le.mp hc).le (momentScale_pos hT).le).trans hM

end ZetaSixth

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Legendre

open Filter MeasureTheory Set
open scoped Topology

theorem integrableOn_rpow_mul_log_tail {p c : ℝ} (hp : 1 ≤ p) (hc : 1 ≤ c) :
    IntegrableOn (fun y : ℝ ↦ y ^ (-p - 1 : ℝ) * Real.log y) (Ioi c) := by
  have hc₀ := zero_lt_one.trans_le hc
  have hM : AEStronglyMeasurable (fun y : ℝ ↦ y ^ (-p - 1 : ℝ) * Real.log y) (volume.restrict (Ioi c)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro y hy
    have h := (hc₀.trans hy).ne'
    exact ((Real.continuousAt_rpow_const y (-p - 1) (.inl h)).mul (Real.continuousAt_log h)).continuousWithinAt
  apply Integrable.mono'
    ((integrableOn_Ioi_rpow_of_lt (a := -p - 1 + 1 / 2) (by linarith) hc₀).const_mul 2) hM
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
  have hy₀ := hc₀.trans hy
  have hlog : 0 ≤ Real.log y := Real.log_nonneg (hc.trans hy.le)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hy₀.le _) hlog), Real.rpow_add hy₀]
  calc
    _ ≤ y ^ (-p - 1 : ℝ) * (y ^ (1 / 2 : ℝ) / (1 / 2)) :=
      mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hy₀.le (by norm_num)) (Real.rpow_nonneg hy₀.le _)
    _ = _ := by ring

/-- Integral of a logarithm times a power over the positive tail. -/
theorem integral_rpow_mul_log_tail {p c : ℝ} (hp : 1 ≤ p) (hc : 1 ≤ c) :
    (∫ y in Ioi c, y ^ (-p - 1 : ℝ) * Real.log y) =
      c ^ (-p) / p * (Real.log c + 1 / p) := by
  have hp₀ := zero_lt_one.trans_le hp
  let H : ℝ → ℝ := fun y ↦ -(y ^ (-p) * (Real.log y / p + 1 / p ^ 2))
  have hd : ∀ y ∈ Ici c, HasDerivAt H (y ^ (-p - 1 : ℝ) * Real.log y) y := by
    intro y hy
    have hy₀ : 0 < y := (zero_lt_one.trans_le hc).trans_le hy
    have hpow := Real.hasDerivAt_rpow_const (p := -p) (Or.inl hy₀.ne')
    have hlog := ((Real.hasDerivAt_log hy₀.ne').div_const p).add_const (1 / p ^ 2)
    have h := (hpow.mul hlog).neg
    convert h using 1
    rw [Real.rpow_sub hy₀, Real.rpow_one]
    field_simp [hy₀.ne', hp₀.ne']
    ring
  have ht₁ := (isLittleO_log_rpow_atTop hp₀).tendsto_div_nhds_zero
  have ht₂ := tendsto_rpow_neg_atTop hp₀
  have hlim : Tendsto H atTop (𝓝 0) := by
    have ht := ((ht₁.div_const p).add (ht₂.div_const (p ^ 2))).neg
    simp only [zero_div, add_zero, neg_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    dsimp [H]
    rw [Real.rpow_neg hy.le]
    ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_rpow_mul_log_tail hp hc) hlim]
  dsimp [H]
  field_simp [hp₀.ne']
  ring

end Legendre

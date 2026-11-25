import ZetaSixth.Claims
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.Linarith

namespace ZetaSixth

open MeasureTheory Set

namespace Weight

theorem continuous (Φ : Weight) : Continuous Φ.toFun := Φ.smooth.continuous

theorem integrable (Φ : Weight) : Integrable Φ.toFun :=
  Φ.continuous.integrable_of_hasCompactSupport Φ.compactSupport

theorem integral_pos (Φ : Weight) : 0 < ∫ t, Φ t := by
  obtain ⟨t, ht⟩ := Φ.nonzero
  exact Φ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    Φ.compactSupport Φ.nonnegative ht

theorem zero_of_notMem (Φ : Weight) {t : ℝ} (ht : t ∉ Ioo (1 : ℝ) 2) : Φ t = 0 := by
  by_contra hn
  exact ht (Φ.supportInside (subset_tsupport Φ.toFun hn))

private noncomputable def ofBump (b : ContDiffBump (3 / 2 : ℝ)) (hb : b.rOut < 1 / 2) :
    Weight where
  toFun := b
  smooth := b.contDiff
  nonnegative := b.nonneg'
  compactSupport := b.hasCompactSupport
  supportInside := by
    rw [b.tsupport_eq, Real.closedBall_eq_Icc]
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  nonzero := by
    refine ⟨3 / 2, ?_⟩
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    exact one_ne_zero

/-- Smooth admissible weights can approximate the indicator of `(1, 2)` in integral. -/
theorem exists_integral_gt {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1) :
    ∃ Φ : Weight, (∀ t, Φ t ≤ 1) ∧ 1 - ε < ∫ t, Φ t := by
  let b : ContDiffBump (3 / 2 : ℝ) :=
    ⟨1 / 2 - ε / 4, 1 / 2 - ε / 8, by linarith, by linarith⟩
  let Φ := ofBump b (by change 1 / 2 - ε / 8 < 1 / 2; linarith)
  let s := Metric.closedBall (3 / 2 : ℝ) b.rIn
  have hs : MeasurableSet s := Metric.isClosed_closedBall.measurableSet
  have hOn : EqOn (fun _ => (1 : ℝ)) Φ.toFun s :=
    fun _ ht => (b.one_of_mem_closedBall ht).symm
  have hMeasure : volume.real s = 2 * b.rIn := by
    rw [Measure.real, show s = Icc (3 / 2 - b.rIn) (3 / 2 + b.rIn) from
      Real.closedBall_eq_Icc, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [b.rIn_pos])]
    ring
  refine ⟨Φ, fun t => b.le_one, ?_⟩
  calc
    1 - ε < 2 * b.rIn := by change 1 - ε < 2 * (1 / 2 - ε / 4); linarith
    _ = ∫ _ in s, (1 : ℝ) := by rw [setIntegral_const, hMeasure, smul_eq_mul, mul_one]
    _ = ∫ t in s, Φ t := setIntegral_congr_fun hs hOn
    _ ≤ ∫ t, Φ t := setIntegral_le_integral Φ.integrable (ae_of_all _ Φ.nonnegative)

end Weight

/-- The quantification over time weights in Definition 7 has actual smooth witnesses. -/
theorem nonempty_weight : Nonempty Weight := by
  obtain ⟨Φ, _, _⟩ := Weight.exists_integral_gt (ε := 1 / 2) (by norm_num) (by norm_num)
  exact ⟨Φ⟩

end ZetaSixth

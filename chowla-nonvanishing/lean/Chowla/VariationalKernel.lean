import Chowla.VariationalSquare
import Chowla.Model.Rows
import Mathlib.Analysis.Calculus.BumpFunction.Normed

namespace Chowla

open Filter Function MeasureTheory Set
open scoped Topology

private noncomputable def variationalBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private theorem support_variationalBump : support (variationalBump : ℝ → ℝ) ⊆ Icc (-(1 / 2)) (1 / 2) := by
  rw [variationalBump.support_eq]
  intro u hu
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hu
  exact abs_le.mp hu.le

/-- An even, nonnegative smooth Fourier kernel of integral one. -/
noncomputable def variationalKernel : SmoothProfile where
  profile := variationalBump.normed volume
  isProfile := ⟨variationalBump.continuous_normed.measurable, variationalBump.normed_neg,
    (variationalBump.hasCompactSupport_normed.isCompact_range variationalBump.continuous_normed).isBounded,
    variationalBump.hasCompactSupport_normed⟩
  smooth := variationalBump.contDiff_normed

theorem variationalKernel_nonnegative (u : ℝ) : 0 ≤ variationalKernel.profile u :=
  variationalBump.nonneg_normed _

theorem variationalKernel_mass : (∫ u : ℝ, variationalKernel.profile u) = 1 :=
  variationalBump.integral_normed

theorem variationalKernel_support : support variationalKernel.profile ⊆ Icc (-1) 1 := by
  change support (variationalBump.normed volume) ⊆ _
  rw [variationalBump.support_normed_eq, ← variationalBump.support_eq]
  exact support_variationalBump.trans (Icc_subset_Icc (by norm_num) (by norm_num))

theorem variationalKernel_radius : HasRadiusAtMost variationalKernel.profile 1 :=
  ⟨zero_le_one, Eventually.of_forall fun _ hx => notMem_support.mp (fun h => hx (variationalKernel_support h))⟩

private theorem bump_cumulant_pos : 0 < cumulant [(variationalBump : ℝ → ℝ)] := by
  rw [cumulant, variationalBump.one_of_mem_closedBall (Metric.mem_closedBall_self variationalBump.rIn_pos.le)]
  have hb₀ : IntervalIntegrable (variationalBump : ℝ → ℝ) volume 0 (1 / 2) :=
    variationalBump.continuous.intervalIntegrable _ _
  have hb₁ : IntervalIntegrable (variationalBump : ℝ → ℝ) volume (1 / 2) 1 :=
    variationalBump.continuous.intervalIntegrable _ _
  have hzero : (∫ u in (1 / 2 : ℝ)..1, variationalBump u) = 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro u hu
    exact notMem_support.mp (by
      intro hm
      exact hu.1.not_ge (support_variationalBump hm).2)
  have hle : (∫ u in (0 : ℝ)..(1 / 2), variationalBump u) ≤ 1 / 2 := by
    calc
      _ ≤ ∫ _ in (0 : ℝ)..(1 / 2), (1 : ℝ) := intervalIntegral.integral_mono_on (by norm_num)
        hb₀ (continuous_const.intervalIntegrable _ _) (fun _ _ => variationalBump.le_one)
      _ = _ := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals hb₀ hb₁, hzero, add_zero]
  linarith

/-- The one-point correlation implies eventual positive weight in each class. -/
theorem eventually_weightedMass_pos_of_moments (m : PaperClaims) (D : DiscClass) (W : ShellWeight) :
    ∀ᶠ X in atTop, 0 < weightedSum D W X (fun _ => 1) := by
  let h : FourierProfile := variationalBump
  have hp : IsProfile h := ⟨variationalBump.continuous.measurable, variationalBump.neg,
    (variationalBump.hasCompactSupport.isCompact_range variationalBump.continuous).isBounded,
    variationalBump.hasCompactSupport⟩
  let t := MomentTest.ofProfile h hp variationalBump.contDiff
  have hr : MomentWord.bandwidth [t] < 2 := by
    simp only [MomentWord.bandwidth, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      t, MomentTest.ofProfile_profile]
    exact (radius_le_of_hasRadiusAtMost ⟨by norm_num, Eventually.of_forall fun x hx =>
      notMem_support.mp (fun hm => hx (support_variationalBump hm))⟩).trans_lt (by norm_num)
  have hm := momentWord_limit m D W [t] (by simp) hr
  have hmodel : modelExpectation (MomentWord.model [t]) = cumulant [h] := by
    rw [show MomentWord.model [t] = stat h from by
      simp [MomentWord.model, t, MomentTest.ofProfile_profile]]
    exact modelExpectation_singleton h hp
  rw [hmodel] at hm
  filter_upwards [hm.eventually (Ioi_mem_nhds bump_cumulant_pos)] with X hX
  exact lt_of_le_of_ne (weightedMass_nonneg D W X) (Ne.symm fun hzero => by
    simp [weightedAverage, hzero] at hX)

end Chowla

import Chowla.CountingClasses
import Chowla.VariationalWeighted
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace Chowla

open Filter MeasureTheory
open scoped BigOperators Topology NNReal

noncomputable def classDensity (D : DiscClass) : ℝ :=
  match D.2 with
  | .odd | .four => 2 / Real.pi^2
  | .eight => 4 / Real.pi^2

theorem classDensity_pos (D : DiscClass) : 0 < classDensity D := by
  have hp := Real.pi_pos
  unfold classDensity
  cases D.2 <;> positivity

noncomputable def sharpShell (D : DiscClass) (X : ℝ) : Finset ℤ :=
  (classDiscs D (2 * (D.2.kappa : ℝ) * X)).filter (fun d => X < oddPart D d)

theorem ShellWeight.zero_off_interval (W : ShellWeight) {x : ℝ} (hx : x ∉ Set.Ioo 1 2) :
    W.toFun x = 0 := by
  by_contra hn
  exact hx (W.supported (subset_tsupport _ hn))

theorem ShellWeight.integral_pos (W : ShellWeight) : 0 < ∫ x : ℝ, W.toFun x := by
  have hi : Integrable W.toFun volume := W.smooth.continuous.integrable_of_hasCompactSupport W.compact
  refine (integral_pos_iff_support_of_nonneg W.nonnegative hi).mpr ?_
  have hopen : IsOpen (Function.support W.toFun) :=
    W.smooth.continuous.isOpen_support
  have hne : (Function.support W.toFun).Nonempty := by
    by_contra! h
    apply W.nonzero
    funext x
    exact Function.notMem_support.mp (by simp [h])
  exact hopen.measure_pos volume hne

/-- A smooth weight supported in the open shell with a plateau whose length is `1 - e`. -/
theorem exists_shellWeight_large_integral (e : ℝ) (he : 0 < e) (he' : e < 1) :
    ∃ W : ShellWeight, (∀ x, W.toFun x ≤ 1) ∧ 1 - e ≤ ∫ x : ℝ, W.toFun x := by
  let B : ContDiffBump (3 / 2 : ℝ) :=
    ⟨(1 - e) / 2, (1 - e / 2) / 2, by linarith, by linarith⟩
  let W : ShellWeight :=
    { toFun := B
      smooth := B.contDiff
      compact := B.hasCompactSupport
      supported := by
        rw [B.tsupport_eq]
        intro x hx
        have h := (Metric.mem_closedBall.mp hx)
        rw [Real.dist_eq] at h
        have hc := abs_le.mp h
        dsimp [B] at hc
        exact ⟨by linarith [hc.1], by linarith [hc.2]⟩
      nonnegative := B.nonneg'
      nonzero := by
        intro hn
        have h := B.one_of_mem_closedBall (Metric.mem_closedBall_self B.rIn_pos.le)
        exact one_ne_zero (h.symm.trans (congrFun hn (3/2))) }
  refine ⟨W, fun _ => B.le_one, ?_⟩
  let S := Metric.closedBall (3 / 2 : ℝ) B.rIn
  have hSi : Integrable (S.indicator (fun _ : ℝ => (1 : ℝ))) :=
    integrable_indicator_iff measurableSet_closedBall |>.mpr <|
      integrableOn_const (C := (1 : ℝ)) (isCompact_closedBall (3 / 2 : ℝ) B.rIn).measure_ne_top
  have hWi : Integrable W.toFun volume := W.smooth.continuous.integrable_of_hasCompactSupport W.compact
  have hdom (x : ℝ) : S.indicator (fun _ : ℝ => (1 : ℝ)) x ≤ W.toFun x := by
    by_cases hs : x ∈ S
    · rw [Set.indicator_of_mem hs]
      exact (B.one_of_mem_closedBall hs).ge
    · rw [Set.indicator_of_notMem hs]
      exact W.nonnegative x
  have hval : (∫ x : ℝ, S.indicator (fun _ : ℝ => (1 : ℝ)) x) = 1 - e := by
    rw [integral_indicator measurableSet_closedBall, setIntegral_const]
    simp only [smul_eq_mul, mul_one]
    change (volume S).toReal = 1 - e
    rw [Real.volume_closedBall, ENNReal.toReal_ofReal (mul_nonneg (by norm_num) B.rIn_pos.le)]
    dsimp [B]
    ring
  rw [← hval]
  exact integral_mono hSi hWi hdom

theorem weighted_nonvanishing_le_sharpShell (D : DiscClass) (W : ShellWeight) {X : ℝ}
    (hX : 0 < X) (hW : ∀ x, W.toFun x ≤ 1) :
    weightedSum D W X nonvanishingIndicator ≤ ((nonvanishing (sharpShell D X)).card : ℝ) := by
  classical
  unfold weightedSum sharpShell nonvanishing
  rw [Finset.filter_filter, ← Finset.sum_boole]
  refine Finset.sum_le_sum fun d _ => ?_
  by_cases hd : X < oddPart D d
  · by_cases hn : CentralNonvanishing d
    · simpa [hd, nonvanishingIndicator, hn] using hW (oddPart D d / X)
    · simp [nonvanishingIndicator, hn]
  · have hx : oddPart D d / X ≤ 1 := (div_le_iff₀ hX).mpr (by simpa using le_of_not_gt hd)
    have hz : W.toFun (oddPart D d / X) = 0 :=
      W.zero_off_interval (fun h => (not_lt_of_ge hx) h.1)
    simp [hz, hd]

/-- The exact shell mass formula implies the order-X mass is eventually positive. -/
theorem eventually_weightedMass_pos_of_limit (D : DiscClass) (W : ShellWeight)
    (hMass : Tendsto (fun X => weightedSum D W X (fun _ => 1) / X) atTop
      (𝓝 (classDensity D * ∫ u : ℝ, W.toFun u))) :
    ∀ᶠ X in atTop, 0 < weightedSum D W X (fun _ => 1) := by
  have hpos := mul_pos (classDensity_pos D) W.integral_pos
  have h : ∀ᶠ X in atTop, 0 < weightedSum D W X (fun _ => 1) / X :=
    hMass.eventually (Ioi_mem_nhds hpos)
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with X hX hposX
  exact ((div_pos_iff.mp hX).resolve_right (fun h => hposX.not_gt h.2)).1

/-- Removing `W` from a dyadic shell only costs the difference between its smooth
mass and the sharp shell mass. -/
theorem sharpShell_mass_deficit_of_limits (D : DiscClass) (W : ShellWeight)
    (hMass : Tendsto (fun X => weightedSum D W X (fun _ => 1) / X) atTop
      (𝓝 (classDensity D * ∫ u : ℝ, W.toFun u)))
    (hShell : Tendsto (fun X => ((sharpShell D X).card : ℝ) / X) atTop (𝓝 (classDensity D))) :
    Tendsto (fun X : ℝ =>
      (((sharpShell D X).card : ℝ) - weightedSum D W X (fun _ => 1)) / X) atTop
      (𝓝 (classDensity D * (1 - ∫ u : ℝ, W.toFun u))) := by
  convert hShell.sub hMass using 2
  · exact sub_div _ _ _
  · ring

end Chowla

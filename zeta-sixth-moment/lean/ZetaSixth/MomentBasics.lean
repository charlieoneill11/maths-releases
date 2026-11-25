import ZetaSixth.Euler
import ZetaSixth.Weights
import Mathlib.Tactic.FunProp

namespace ZetaSixth

open MeasureTheory

theorem continuous_zetaLine : Continuous zetaLine := by
  rw [continuous_iff_continuousAt]
  intro t
  have ht : (1 : ℂ) / 2 + (t : ℂ) * Complex.I ≠ 1 := by
    intro he
    have hre := congrArg Complex.re he
    norm_num [Complex.div_re, Complex.mul_re, Complex.add_re] at hre
  have hcont : ContinuousAt (fun x : ℝ => (1 : ℂ) / 2 + (x : ℂ) * Complex.I) t := by
    fun_prop
  unfold zetaLine
  exact (differentiableAt_riemannZeta ht).continuousAt.comp_of_eq hcont rfl

noncomputable def momentDensity (t : ℝ) : ℝ := ‖zetaLine t‖ ^ 6

theorem continuous_momentDensity : Continuous momentDensity := continuous_zetaLine.norm.pow 6

theorem momentDensity_nonnegative (t : ℝ) : 0 ≤ momentDensity t := by
  exact pow_nonneg (norm_nonneg _) _

noncomputable def momentScale (T : ℝ) : ℝ := c3 * T * Real.log T ^ 9

theorem momentScale_pos {T : ℝ} (hT : 1 < T) : 0 < momentScale T :=
  mul_pos (mul_pos c3_pos (zero_lt_one.trans hT)) (pow_pos (Real.log_pos hT) 9)

theorem timeNorm_eq (Φ : Weight) (T : ℝ) :
    timeNorm Φ T = (Nat.factorial 9 : ℝ) * momentScale T * ∫ t, Φ t := by
  have hc : (Nat.factorial 9 : ℝ) * c3 = a3 := by
    have h₉ : (Nat.factorial 9 : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos 9).ne'
    unfold c3
    field_simp
  unfold timeNorm momentScale
  rw [← hc]
  ring

theorem timeNorm_pos (Φ : Weight) {T : ℝ} (hT : 1 < T) : 0 < timeNorm Φ T := by
  rw [timeNorm_eq]
  exact mul_pos (mul_pos (by exact_mod_cast Nat.factorial_pos 9) (momentScale_pos hT))
    Φ.integral_pos

theorem Weight.continuous_rescale (Φ : Weight) (T : ℝ) :
    Continuous (fun t => Φ (t / T)) :=
  Φ.continuous.comp (continuous_id.div_const T)

theorem Weight.compactSupport_rescale (Φ : Weight) (T : ℝ) :
    HasCompactSupport (fun t => Φ (t / T)) := by
  by_cases hT : T = 0
  · have h0 : Φ 0 = 0 := Φ.zero_of_notMem (by norm_num)
    simpa [hT, h0] using (HasCompactSupport.zero : HasCompactSupport (0 : ℝ → ℝ))
  · simpa only [Function.comp_apply, div_eq_mul_inv, Homeomorph.coe_mulRight₀] using
      Φ.compactSupport.comp_homeomorph (Homeomorph.mulRight₀ T⁻¹ (inv_ne_zero hT))

noncomputable def smoothedMoment (Φ : Weight) (T : ℝ) : ℝ :=
  ∫ t, Φ (t / T) * momentDensity t

theorem smoothIntegrable (Φ : Weight) (T : ℝ) :
    Integrable (fun t => Φ (t / T) * momentDensity t) :=
  ((Φ.continuous_rescale T).mul continuous_momentDensity).integrable_of_hasCompactSupport
    (Φ.compactSupport_rescale T).mul_right

end ZetaSixth

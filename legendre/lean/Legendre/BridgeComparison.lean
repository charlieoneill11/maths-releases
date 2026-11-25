import Legendre.BridgeData
import Legendre.Geometry

namespace Legendre

private theorem root_growth {l x : ℝ} (hl : 0 < l) (hx : 0 < x) :
    l ^ ((1 : ℝ) / 10) * (1 + (Real.log x - Real.log l) / 10) ≤ x ^ ((1 : ℝ) / 10) := by
  have heq : x ^ ((1 : ℝ) / 10) =
      l ^ ((1 : ℝ) / 10) * Real.exp ((Real.log x - Real.log l) / 10) := by
    rw [Real.rpow_def_of_pos hl, Real.rpow_def_of_pos hx, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [add_comm] using (Real.add_one_le_exp ((Real.log x - Real.log l) / 10)))
    (Real.rpow_nonneg hl.le _)

/-- The lower bound checked at the left endpoint ensures monotonicity to its right. -/
theorem bridgeComparison_mono_of_slope {k l x : ℝ} (hk : 0 ≤ k) (hl : 0 < l) (hlx : l ≤ x)
    (hslope : 0 ≤ 0.11 * k * l ^ ((1 : ℝ) / 10) * (l / (l + 1)) - 0.765870) :
    bridgeComparison k l ≤ bridgeComparison k x := by
  have hx : 0 < x := hl.trans_le hlx
  have hu : 0 ≤ Real.log x - Real.log l := sub_nonneg.mpr (Real.log_le_log hl hlx)
  have hfrac : l / (l + 1) ≤ x / (x + 1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hterm : l ^ ((1 : ℝ) / 10) * (l / (l + 1)) *
      (1 + (Real.log x - Real.log l) / 10) ≤ x ^ ((1 : ℝ) / 10) * (x / (x + 1)) := by
    calc
      _ = (l ^ ((1 : ℝ) / 10) * (1 + (Real.log x - Real.log l) / 10)) * (l / (l + 1)) := by ring
      _ ≤ _ := mul_le_mul (root_growth hl hx) hfrac (by positivity) (Real.rpow_nonneg hx.le _)
  have hlog : Real.log ((x + 1) / 1.1) - Real.log ((l + 1) / 1.1) ≤
      Real.log x - Real.log l := by
    have hx' : x + 1 ≠ 0 := by positivity
    have hl' : l + 1 ≠ 0 := by positivity
    have hs : (1.1 : ℝ) ≠ 0 := by norm_num
    rw [Real.log_div hx' hs, Real.log_div hl' hs]
    rw [show Real.log (x + 1) - Real.log 1.1 - (Real.log (l + 1) - Real.log 1.1) =
      Real.log (x + 1) - Real.log (l + 1) by ring]
    rw [← Real.log_div hx' hl', ← Real.log_div hx.ne' hl.ne']
    apply Real.log_le_log (by positivity)
    exact (div_le_div_iff₀ (by positivity) hl).2 (by nlinarith)
  have hmul := mul_le_mul_of_nonneg_left hterm (show 0 ≤ (1.1 : ℝ) * k by positivity)
  have hcorrect := mul_nonneg hslope hu
  unfold bridgeComparison
  nlinarith only [hmul, hcorrect, hlog]

theorem BridgeRowChecks.window_bounds {row : BridgeRow} {e : ℕ → ℚ} {b : ℕ → ℝ}
    (h : BridgeRowChecks row e b) (hl : 0 < row.lo) (hP : 0 < row.scaleLo)
    {x : ℝ} (hx₁ : (row.lo : ℝ) ≤ x) (hx₂ : x ≤ (row.hi : ℝ)) :
    (row.logLo : ℝ) ≤ (Window.ofBase x).L ∧ (Window.ofBase x).L ≤ (row.logHi : ℝ) ∧
      (row.scaleLo : ℝ) ≤ (Window.ofBase x).P ∧ 4000 * U₁ < (Window.ofBase x).W := by
  have hl' : 0 < (row.lo : ℝ) := by exact_mod_cast hl
  have hx := hl'.trans_le hx₁
  have hP' : 0 < (row.scaleLo : ℝ) := by exact_mod_cast hP
  have hlog₁ : Real.log row.lo ≤ Real.log x := Real.log_le_log hl' hx₁
  have hlog₂ : Real.log (x + 1) ≤ Real.log ((row.hi : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hL := Window.ofBase_L_bounds hx
  have hscale : (row.scaleLo : ℝ) ≤ (Window.ofBase x).P := by
    refine h.scaleLo.le.trans (?_ : 1.1 * (row.lo : ℝ) ^ ((1 : ℝ) / 10) *
      ((row.lo : ℝ) / ((row.lo : ℝ) + 1)) ≤ (Window.ofBase x).P)
    have hm := mul_le_mul_of_nonneg_left (scaleFactor_mono hl' hx₁) (by norm_num : (0 : ℝ) ≤ 1.1)
    rw [← mul_assoc, ← mul_assoc] at hm
    exact hm.trans (Window.ofBase_P_bounds hx).1
  have hroot : (row.lo : ℝ) * (row.lo : ℝ) ^ ((1 : ℝ) / 10) ≤
      Real.sqrt (Window.ofBase x).a := by
    calc
      _ = (row.lo : ℝ) ^ ((11 : ℝ) / 10) := by
        rw [show (11 / 10 : ℝ) = 1 / 10 + 1 by norm_num, Real.rpow_add_one hl'.ne', mul_comm]
      _ ≤ x ^ ((11 : ℝ) / 10) := Real.rpow_le_rpow hl'.le hx₁ (by norm_num)
      _ ≤ _ := (Window.ofBase_sqrt_bounds hx).1
  refine ⟨by linarith [h.logLo, hL.1], by linarith [h.logHi, hL.2], hscale, ?_⟩
  have hWlim : (row.scaleLo : ℝ) * (row.lo : ℝ) * (row.lo : ℝ) ^ ((1 : ℝ) / 10) ≤
      (Window.ofBase x).W := by
    rw [Window.ofBase_W_eq hx, mul_assoc]
    exact mul_le_mul hscale hroot (by positivity) ((hP'.trans_le hscale).le)
  exact (show (4000 : ℝ) * U₁ ≤ 4000 * U₁ * 10 ^ 12 by norm_num [U₁]).trans_lt
    (h.lengthLo.trans_le hWlim)

theorem BridgeRowChecks.comparison_pos {row : BridgeRow} {e : ℕ → ℚ} {b : ℕ → ℝ}
    (h : BridgeRowChecks row e b) (hl : 0 < row.lo) (hk : 0 ≤ row.k)
    (hv : 0 ≤ row.valueLo) (hd : 0 ≤ row.derivLo) {x : ℝ} (hx : (row.lo : ℝ) ≤ x) :
    0 < bridgeComparison row.k x := by
  have hv' : 0 ≤ (row.valueLo : ℝ) := by exact_mod_cast hv
  have hd' : 0 ≤ (row.derivLo : ℝ) := by exact_mod_cast hd
  exact (hv'.trans_lt h.comparison).trans_le <|
    bridgeComparison_mono_of_slope (by exact_mod_cast hk) (by exact_mod_cast hl) hx (hd'.trans h.derivative.le)

end Legendre

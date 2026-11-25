import Legendre.Geometry
import Legendre.Arithmetic.BridgeNumeric

namespace Legendre

open Real Arithmetic

/-- Uniform bound on the errors in Proposition 22 from rational input bounds. -/
theorem bridge_errors_le_of_bounds {x : ℝ} (hx₁ : 35 * 10 ^ 12 ≤ x) (hx₂ : x ≤ 6 * 10 ^ 14)
    (hL : (Window.ofBase x).L ≤ 37.5) (e : ℕ → ℚ) (he : ShoulderSteps e)
    (minSqrt log2Lo logArgHi : ℝ) (hmin : 0 < minSqrt)
    (hroot : minSqrt ≤ (35 * 10 ^ 12 : ℝ) ^ ((11 : ℝ) / 10))
    (hlog2Pos : 0 < log2Lo) (hlog2 : log2Lo ≤ Real.log 2)
    (hlogArg : Real.log (7 / (1.1 / (6 * 10 ^ 14 + 1))) ≤ logArgHi) :
    let w := Window.ofBase x
    primePowerError w 2 + 2 * w.D *
        ((3 + 0.15 * Real.log (2 * Real.pi / w.D)) * 625 + 0.15 * 2000 + 4) +
      4 * U ^ 2 * (e 1 : ℝ) * 37.5 * Real.exp (-w.L) + 1 / 10 ^ 12 ≤
    (2 + 76 / log2Lo * (1 + 68 * U)) * 76 * U / minSqrt +
      2 * (1.1 / (35 * 10 ^ 12)) * ((3 + 0.15 * logArgHi) * 625 + 300 + 4) +
      4 * U ^ 2 * 0.76 * 37.5 / minSqrt + 1 / 10 ^ 12 := by
  let w := Window.ofBase x
  change primePowerError w 2 + 2 * w.D *
        ((3 + 0.15 * Real.log (2 * Real.pi / w.D)) * 625 + 0.15 * 2000 + 4) +
      4 * U ^ 2 * (e 1 : ℝ) * 37.5 * Real.exp (-w.L) + 1 / 10 ^ 12 ≤ _
  have hx : 0 < x := (by norm_num : (0 : ℝ) < 35 * 10 ^ 12).trans_le hx₁
  obtain ⟨hw, hP⟩ := bridge_window_bounds hx₁ hx₂
  have hU : 0 < U := by norm_num [U]
  have hSa : minSqrt ≤ Real.sqrt w.a :=
    hroot.trans <| (rpow_le_rpow (by norm_num) hx₁ (by norm_num : (0 : ℝ) ≤ 11 / 10)).trans
      (Window.ofBase_sqrt_bounds hx).1
  have hDhi : w.D ≤ 1.1 / (35 * 10 ^ 12) :=
    (Window.ofBase_D_bounds hx).2.trans <| div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx₁
  have hDlo : 1.1 / (6 * 10 ^ 14 + 1) ≤ w.D :=
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)).trans
      (Window.ofBase_D_bounds hx).1
  have hDsmall : w.D ≤ 1 / 2 := hDhi.trans (by norm_num)
  have hlogLo : 0 ≤ Real.log (2 * Real.pi / w.D) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hw.D_pos, one_mul]
    linarith [Real.pi_gt_three]
  have hlogHi : Real.log (2 * Real.pi / w.D) ≤ logArgHi := by
    have hπ : 2 * Real.pi ≤ 7 := by
      have h := Legendre.Arithmetic.piBounds_sound.2
      norm_num [Legendre.Arithmetic.piBounds] at h
      linarith
    refine (Real.log_le_log (by positivity [hw.D_pos]) (?_ : 2 * Real.pi / w.D ≤ _)).trans hlogArg
    exact div_le_div₀ (by positivity) hπ (by norm_num) hDlo
  let ell := Real.log w.a + 2 * w.D
  have hell : 0 ≤ ell := by dsimp [ell]; linarith [hw.log_a, hw.D_pos]
  have hellHi : ell ≤ 76 := by
    dsimp only [ell]
    rw [w.log_a_eq_two_L hw.a_pos.le]
    change w.L ≤ 37.5 at hL
    linarith
  have hPnonneg : 0 ≤ w.P := mul_nonneg hw.D_pos.le (sqrt_nonneg _)
  have hpow : primePowerError w 2 ≤
      (2 + 76 / log2Lo * (1 + 68 * U)) * 76 * U / minSqrt := by
    have hratio : ell / Real.log 2 ≤ 76 / log2Lo :=
      div_le_div₀ (by norm_num) hellHi hlog2Pos hlog2
    have hcount : 1 + 2 * w.P * U ≤ 1 + 68 * U := by
      linarith [mul_le_mul_of_nonneg_right hP.le hU.le]
    have hfac : 2 + ell / Real.log 2 * (1 + 2 * w.P * U) ≤ 2 + 76 / log2Lo * (1 + 68 * U) :=
      add_le_add_right (mul_le_mul hratio hcount (by positivity) (by positivity)) 2
    change (2 + ell / Real.log 2 * (1 + 2 * w.P * U)) * ell * U / Real.sqrt w.a ≤ _
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right
      (mul_le_mul hfac hellHi hell (by positivity)) hU.le) hmin hSa
  have hzeros : 2 * w.D * ((3 + 0.15 * Real.log (2 * Real.pi / w.D)) * 625 + 0.15 * 2000 + 4) ≤
      2 * (1.1 / (35 * 10 ^ 12)) * ((3 + 0.15 * logArgHi) * 625 + 300 + 4) := by
    have hco : (3 + 0.15 * Real.log (2 * Real.pi / w.D)) * 625 + 0.15 * 2000 + 4 ≤
        (3 + 0.15 * logArgHi) * 625 + 300 + 4 := by linarith
    exact mul_le_mul (by linarith) hco (by positivity) (by positivity)
  have hshoulder : 4 * U ^ 2 * (e 1 : ℝ) * 37.5 * Real.exp (-w.L) ≤
      4 * U ^ 2 * 0.76 * 37.5 / minSqrt := by
    have he₁ : (e 1 : ℝ) ≤ 0.76 := by
      rw [← show ((0.76 : ℚ) : ℝ) = 0.76 by norm_num]
      exact_mod_cast he.first.le
    have he₀ : 0 ≤ (e 1 : ℝ) := by exact_mod_cast he.nonneg 1 (by decide) (by decide)
    rw [Real.exp_neg, w.exp_L_eq_sqrt hw.a_pos, ← div_eq_mul_inv]
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he₁ (by positivity)) (by norm_num)) hmin hSa
  linarith only [hpow, hzeros, hshoulder]

theorem bridge_error_bounds (e : ℕ → ℚ) (he : ShoulderSteps e) (x : ℝ)
    (hx₁ : 35 * 10 ^ 12 ≤ x) (hx₂ : x ≤ 6 * 10 ^ 14) (hL : (Window.ofBase x).L ≤ 37.5) :
    let w := Window.ofBase x
    primePowerError w twelveMode.K + 2 * w.D *
        ((3 + 0.15 * Real.log (2 * Real.pi / w.D)) * 625 + 0.15 * 2000 + 4) +
      4 * U ^ 2 * (e 1 : ℝ) * 37.5 * Real.exp (-w.L) + 1 / 10 ^ 12 < 1.1 / 10 ^ 9 := by
  have hr : (bridgeErrorData.minSqrt : ℝ) ≤ (35 * 10 ^ 12 : ℝ) ^ ((11 : ℝ) / 10) := by
    rw [show (11 / 10 : ℝ) = 1 / 10 + 1 by norm_num, Real.rpow_add_one (by norm_num), mul_comm]
    exact bridgeMinSqrt_le
  have hdlo : (bridgeErrorData.minD : ℝ) = 1.1 / (6 * 10 ^ 14 + 1) := by
    norm_num [bridgeErrorData]
  have hdhi : (bridgeErrorData.maxD : ℝ) = 1.1 / (35 * 10 ^ 12) := by
    norm_num [bridgeErrorData]
  have hlog := bridgeLogArg_le
  rw [hdlo] at hlog
  have h := bridge_errors_le_of_bounds hx₁ hx₂ hL e he _ _ _ bridge_errors.minSqrt_pos hr
    bridge_errors.log2Lo_pos bridgeLog2Lo_le hlog
  exact h.trans_lt (hdhi ▸ bridge_errors.total)

end Legendre

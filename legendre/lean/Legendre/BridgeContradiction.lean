import Legendre.BridgeComparison
import Legendre.BridgeError

namespace Legendre

/-- The contradiction in Proposition 22 for one row of Table 1. -/
theorem bridge_case {x : ℝ} (hx₁ : 35 * 10 ^ 12 ≤ x) (hx₂ : x ≤ 6 * 10 ^ 14)
    (row : BridgeRow) (e : ℕ → ℚ) (b : ℕ → ℝ)
    (he : ShoulderSteps e) (hr : BridgeRowChecks row e b) (hF : TwelveModeEstimates)
    (hl : 0 < row.lo) (hp : 0 < row.scaleLo) (hk : 0 ≤ row.k)
    (hv : 0 ≤ row.valueLo) (hdv : 0 ≤ row.derivLo) (hh : (row.logHi : ℝ) ≤ 37.5)
    (hxl : (row.lo : ℝ) ≤ x) (hxr : x ≤ (row.hi : ℝ)) :
    let w := Window.ofBase x
    shoulderSum w twelveMode ≤ w.P * shoulderCharge e b row.logLo row.logHi +
        4 * U ^ 2 * (e 1 : ℝ) * (row.logHi : ℝ) * Real.exp (-w.L) →
    (¬ PrimeIn (w.endpoint (-1)) (w.endpoint 1) →
      w.P * twelveMode.F 0 ≤ shoulderSum w twelveMode +
        fourierMass twelveMode.F * Real.log (1 / w.D) + logMoment twelveMode.F +
        primePowerError w twelveMode.K + 2 * w.D *
          ((3 + 0.15 * Real.log (2 * Real.pi / w.D)) * totalVariation twelveMode.F +
            0.15 * logVariation twelveMode.F + 4) + 1 / 10 ^ 12) →
    PrimeIn (x ^ ((11 : ℝ) / 5)) ((x + 1) ^ ((11 : ℝ) / 5)) := by
  intro w hshoulder hgap
  have hx : 0 < x := (by norm_num : (0 : ℝ) < 35 * 10 ^ 12).trans_le hx₁
  have hw := (bridge_window_bounds hx₁ hx₂).1
  have hP : 0 ≤ w.P := mul_nonneg hw.D_pos.le (Real.sqrt_nonneg _)
  have hK : (0 : ℝ) ≤ (row.k : ℝ) := by exact_mod_cast hk
  have hL : w.L ≤ 37.5 := (hr.window_bounds hl hp hxl hxr).2.1.trans hh
  have hDsmall : w.D ≤ 1 := by
    have h := hw.width
    change 2 * w.D ≤ (U - 1) / U at h
    norm_num [U] at h
    linarith
  have hlog₀ : 0 ≤ Real.log (1 / w.D) := by
    exact Real.log_nonneg ((le_div_iff₀ hw.D_pos).2 (by simpa using hDsmall))
  have hlogπ : 0 ≤ Real.log (2 * Real.pi / w.D) := by
    apply Real.log_nonneg ((le_div_iff₀ hw.D_pos).2 ?_)
    linarith [Real.pi_gt_three]
  have hcoef : 0 ≤ 3 + 0.15 * Real.log (2 * Real.pi / w.D) := by positivity
  have hvar : 2 * w.D *
      ((3 + 0.15 * Real.log (2 * Real.pi / w.D)) * totalVariation twelveMode.F +
        0.15 * logVariation twelveMode.F + 4) ≤
      2 * w.D * ((3 + 0.15 * Real.log (2 * Real.pi / w.D)) * 625 + 0.15 * 2000 + 4) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity [hw.D_pos])
    linarith only [mul_le_mul_of_nonneg_left hF.variation.le hcoef,
      mul_le_mul_of_nonneg_left hF.log_variation.le (by norm_num : (0 : ℝ) ≤ 0.15)]
  have he₀ : (0 : ℝ) ≤ e 1 := by exact_mod_cast he.nonneg 1 (by decide) (by decide)
  have hshoulder' : shoulderSum w twelveMode ≤ w.P * shoulderCharge e b row.logLo row.logHi +
      4 * U ^ 2 * (e 1 : ℝ) * 37.5 * Real.exp (-w.L) := by
    refine hshoulder.trans (add_le_add_right ?_ _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by positivity)) (by positivity)
  have hsmall := bridge_error_bounds e he x hx₁ hx₂ hL
  have hpole : (row.k : ℝ) ≤ twelveMode.F 0 - shoulderCharge e b row.logLo row.logHi := by
    linarith only [hr.pole, hr.chargeHi, hF.at_zero]
  have hscale : 1.1 * (row.k : ℝ) * x ^ ((1 : ℝ) / 10) * (x / (x + 1)) ≤ w.P * (row.k : ℝ) := by
    calc
      _ = (1.1 * x ^ ((1 : ℝ) / 10) * (x / (x + 1))) * (row.k : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Window.ofBase_P_bounds hx).1 hK
  have hmass := mul_le_mul_of_nonneg_right hF.mass.le hlog₀
  have hlog : 0.765870 * Real.log (1 / w.D) ≤ 0.765870 * Real.log ((x + 1) / 1.1) :=
    mul_le_mul_of_nonneg_left (Window.ofBase_log_inv_D_le hx) (by norm_num)
  have hpole' := mul_le_mul_of_nonneg_left hpole hP
  have hsmall' :
      primePowerError w twelveMode.K + 2 * w.D *
          ((3 + 0.15 * Real.log (2 * Real.pi / w.D)) * 625 + 0.15 * 2000 + 4) +
        4 * U ^ 2 * (e 1 : ℝ) * 37.5 * Real.exp (-w.L) + 1 / 10 ^ 12 < 0.000002 :=
    hsmall.trans (by norm_num)
  have hpos := hr.comparison_pos hl hk hv hdv hxl
  by_contra hnone
  have hept := Window.ofBase_endpoints hx
  have hnone' : ¬ PrimeIn (w.endpoint (-1)) (w.endpoint 1) := by
    change ¬ PrimeIn ((Window.ofBase x).endpoint (-1)) ((Window.ofBase x).endpoint 1)
    simpa only [hept.1, hept.2] using hnone
  have hineq := hgap hnone'
  unfold bridgeComparison at hpos
  nlinarith only [hineq, hshoulder', hvar, hsmall', hF.moment, hpole', hscale, hmass, hlog, hpos]

end Legendre

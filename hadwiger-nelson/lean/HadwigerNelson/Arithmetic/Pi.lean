import HadwigerNelson.Arithmetic.Normalize
import Mathlib.Analysis.Real.Pi.Bounds

/-! Signed periodic means with the rational bounds for π used in the integer star checker. -/

namespace HadwigerNelson.Arithmetic

/-- The release uses this pair of seven-decimal rational bounds for both stars. -/
theorem pi_ticks : (31415926 : ℝ) ≤ 10000000*Real.pi ∧ 10000000*Real.pi ≤ 31415927 := by
  constructor <;> linarith [Real.pi_gt_d20,Real.pi_lt_d20]

/-- Lower integer enclosure after division by the physical angular period 2π. -/
theorem moment_scaled_le (a S q : Int) (hS : 0 < S) (hq : 0 ≤ q) :
    (signedScale a q (2*S*31415926) (2*S*31415927) 10000000 : ℝ) ≤
      (a:ℝ)*q/(2*S*Real.pi) := by
  have hSr : (0:ℝ) < S := by exact_mod_cast hS
  apply signedScale_le _ _ _ _ _ _ hq (by decide) (by positivity)
  · push_cast
    have := mul_le_mul_of_nonneg_left pi_ticks.1 (by positivity : 0 ≤ 2*(S:ℝ))
    linarith only [this]
  · push_cast
    have := mul_le_mul_of_nonneg_left pi_ticks.2 (by positivity : 0 ≤ 2*(S:ℝ))
    linarith only [this]

/-- High precision period enclosure for the complete-wave moments, with K = k * phaseScale. -/
theorem moment_scaled_d20_le (a q K : Int) (hK : 0 < K) (hq : 0 ≤ q) :
    (signedScale a q (K*314159265358979323846) (K*314159265358979323847) (10^20) : ℝ) ≤
      (a:ℝ)*q/(K*Real.pi) := by
  have hKr : (0:ℝ) < K := by exact_mod_cast hK
  have hl : (314159265358979323846 : ℝ) ≤ 10^20*Real.pi := by linarith [Real.pi_gt_d20]
  have hh : 10^20*Real.pi ≤ (314159265358979323847 : ℝ) := by linarith [Real.pi_lt_d20]
  apply signedScale_le _ _ _ _ _ _ hq (by decide) (by positivity)
  · push_cast
    linarith only [mul_le_mul_of_nonneg_left hl hKr.le]
  · push_cast
    linarith only [mul_le_mul_of_nonneg_left hh hKr.le]

end HadwigerNelson.Arithmetic

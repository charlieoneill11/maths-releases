import HadwigerNelson.Angular.Bound
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace HadwigerNelson.Angular

/-- The denominator conversion from the scaled area and the lower bound on π
to the rational probability used in the edge threshold. -/
theorem normalize_probability {p : ℝ} (hp : (314159265358979323846:ℝ)/10^20 ≤ p) :
    (2/(p*(923677693607/10^12)*(1/2))) * ((completeTotal:ℝ)/(10^12)^2) ≤
      (completeUpper:ℝ) := by
  have hpos : (0:ℝ)<p := by
    have low : (0:ℝ) < 314159265358979323846/10^20 := by norm_num
    exact low.trans_le hp
  have small : (0:ℝ) < 923677693607*500000000000*(314159265358979323846/10^20) := by norm_num
  have rewrite :
      (2/(p*(923677693607/10^12)*(1/2))) * ((completeTotal:ℝ)/(10^12)^2) =
        2*(completeTotal:ℝ)/(923677693607*500000000000*p) := by
    field_simp
    ring
  rw [rewrite]
  have low := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2*(completeTotal:ℝ)) small
    (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 923677693607*500000000000))
  apply low.trans
  norm_num [completeTotal,completeUpper]

end HadwigerNelson.Angular

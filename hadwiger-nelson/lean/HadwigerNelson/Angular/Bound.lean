import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

namespace HadwigerNelson.Angular

/-- An upper bound tailored to the edge theorem's argument. -/
def completeUpper : ℚ := 4077152 / 10^12

/-- The largest integer angular sum whose outward probability bound is at most
`completeUpper`, using the 20-place decimal beneath π from `Real.pi_gt_d20`. -/
def completeTotal : Nat := 2957789342482682823

theorem completeUpper_edges : 245510*(completeUpper-(4 / 10^9 : ℚ)) < 1 := by
  norm_num [completeUpper]

theorem completeUpper_milestone : 245269*completeUpper < 1 := by
  norm_num [completeUpper]

theorem completeTotal_normalized :
    2*(completeTotal:ℚ) /
      (923677693607*500000000000*(314159265358979323846 / 10^20)) ≤ completeUpper := by
  norm_num [completeTotal,completeUpper]

end HadwigerNelson.Angular

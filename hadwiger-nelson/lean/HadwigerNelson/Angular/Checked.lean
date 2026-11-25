import HadwigerNelson.Native.Angular.Block003
import HadwigerNelson.Native.Angular.Block004
import HadwigerNelson.Native.Angular.Block005
import HadwigerNelson.Native.Angular.Block006
import HadwigerNelson.Native.Angular.Block007
import HadwigerNelson.Native.Angular.Block008
import HadwigerNelson.Angular.GroupTotals
import HadwigerNelson.Angular.Tails
import Mathlib.Tactic.IntervalCases

namespace HadwigerNelson.Angular

attribute [local irreducible] checkGroup

/-- Computed upper bound for all 268,435,456 angular bins of the complete wave. -/
theorem complete_integer_bound :
    angularSum CompleteWave.profile (2^28) ≤ completeTotal := by
  apply complete_integer_bound_of_groups
  intro k hk
  by_cases middle : 3 ≤ k ∧ k ≤ 8
  · obtain ⟨l,r⟩ := middle
    interval_cases k
    · exact Native.block003
    · exact Native.block004
    · exact Native.block005
    · exact Native.block006
    · exact Native.block007
    · exact Native.block008
  · have outside : k < 3 ∨ 9 ≤ k := by omega
    have h : groupUpper k = 0 := by
      unfold groupUpper
      split <;> omega
    rw [h]
    exact tail_group hk outside

end HadwigerNelson.Angular

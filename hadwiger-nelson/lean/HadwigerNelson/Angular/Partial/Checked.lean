import HadwigerNelson.Native.PartialAngular.Block003
import HadwigerNelson.Native.PartialAngular.Block004
import HadwigerNelson.Native.PartialAngular.Block005
import HadwigerNelson.Native.PartialAngular.Block006
import HadwigerNelson.Native.PartialAngular.Block007
import HadwigerNelson.Native.PartialAngular.Block008
import HadwigerNelson.Angular.Partial.Tails
import Mathlib.Tactic.IntervalCases

namespace HadwigerNelson.Angular.Partial

private def upper : Nat → Nat
  | 3 => 36866779966835711
  | 4 => 70791220128326594
  | 5 => 886673243597054
  | 6 => 67417806072575198
  | 8 => 337950354187155998
  | _ => 0

attribute [local irreducible] checkGroup

/-- The partial edge probability used in the 10,689-point calculation.
The bound applies to any datum with the pinned partial-wave profiles. -/
theorem probability_bound {W : Wave.Datum} (p : Profile W) :
    Placement.meanMonoProb W ≤ 102782566719698111/145001902327661557000000 := by
  apply probability_of_groups p (cover p) upper
  · intro k hk
    by_cases middle : 3≤k ∧ k≤8
    · obtain ⟨l,r⟩ := middle
      interval_cases k
      · exact Native.block003
      · exact Native.block004
      · exact Native.block005
      · exact Native.block006
      · exact Native.block007
      · exact Native.block008
    · have h : upper k=0 := by unfold upper; split <;> omega
      rw [h]
      exact tail_group hk (by omega)
  · have h := rangeSum_spec upper 0 32
    simp only [Nat.zero_add] at h
    rw [←h]
    decide +kernel

theorem datum_probability_bound :
    Placement.meanMonoProb PartialWave.datum ≤ 102782566719698111/145001902327661557000000 :=
  probability_bound datum_profile

end HadwigerNelson.Angular.Partial

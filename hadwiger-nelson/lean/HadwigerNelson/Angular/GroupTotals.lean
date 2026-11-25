import HadwigerNelson.Angular.Checker

namespace HadwigerNelson.Angular

/-- The six nonzero subtotals of the 32 equal angular ranges. -/
def groupUpper : Nat → Nat
  | 3 => 43104663964115033
  | 4 => 505715464716105580
  | 5 => 326792917268440891
  | 6 => 729156026191041238
  | 7 => 194825129595753917
  | 8 => 1158194832531553836
  | _ => 0

/-- Exact rational arithmetic turns the reported subtotals into the cap for
the final angular enclosure. -/
theorem complete_integer_bound_of_groups
    (checked : ∀ k < 32, checkGroup k (groupUpper k) = true) :
    angularSum CompleteWave.profile (2^28) ≤ completeTotal := by
  apply (angularSum_le_groups groupUpper checked).trans
  have eq := rangeSum_spec groupUpper 0 32
  simp only [Nat.zero_add] at eq
  rw [←eq]
  decide +kernel

end HadwigerNelson.Angular

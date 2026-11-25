import LeastPrime.Native.DM1420Lower
import LeastPrime.Native.DM1420Upper
import LeastPrime.Native.DM1519Interior1
import LeastPrime.Native.DM1519Interior2
import LeastPrime.Native.DM1519Interior3
import LeastPrime.Native.DM1519Tail1
import LeastPrime.Native.DM1519Tail2
import LeastPrime.Native.DM1519Tail3
import LeastPrime.Native.DM1519Upper
import LeastPrime.Native.DM1520Interior1
import LeastPrime.Native.DM1520Interior2
import LeastPrime.Native.DM1520Interior3
import LeastPrime.Native.DM1520Tail1
import LeastPrime.Native.DM1520Tail2
import LeastPrime.Native.DM1520Tail3
import LeastPrime.Native.DM1520Upper

/-! The three comparison windows in Table 1. -/

namespace LeastPrime

open Checker Set

private theorem checked_window_bounds {a b lower upper : ℕ}
    (hl : grid lower ≤ p 6 (denote (symmetricWindow a b)))
    (hu : checkWindow .upper 5 a b upper = true) :
    grid lower ≤ p 6 (denote (symmetricWindow a b)) ∧
      q 5 (denote (symmetricWindow a b)) ≤ grid upper :=
  ⟨hl, checkWindow_sound hu⟩

theorem drappeauMounier_14_20 :
    0.596755 ≤ p 6 (Icc 0.14 0.20 ∪ Icc 0.80 0.86) ∧
      q 5 (Icc 0.14 0.20 ∪ Icc 0.80 0.86) ≤ 0.604658 := by
  have h := checked_window_bounds (checkWindow_sound Native.dm1420_lower_checked)
    Native.dm1420_upper_checked
  rw [denote_symmetricWindow (by decide) (by decide)] at h
  norm_num [grid, unit] at h ⊢
  exact h

theorem drappeauMounier_15_19 :
    0.530857 ≤ p 6 (Icc 0.15 0.19 ∪ Icc 0.81 0.85) ∧
      q 5 (Icc 0.15 0.19 ∪ Icc 0.81 0.85) ≤ 0.544968 := by
  have hl := checkLowerSixSlices_sound (a := 150000) (b := 190000)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    Native.dm1519_interior1_checked Native.dm1519_interior2_checked Native.dm1519_interior3_checked
    Native.dm1519_tail1_checked Native.dm1519_tail2_checked Native.dm1519_tail3_checked
  have h := checked_window_bounds hl Native.dm1519_upper_checked
  rw [denote_symmetricWindow (by decide) (by decide)] at h
  norm_num [grid, lowerSliceRound, quotient, unit] at h ⊢
  exact h

theorem drappeauMounier_15_20 :
    0.561986 ≤ p 6 (Icc 0.15 0.20 ∪ Icc 0.80 0.85) ∧
      q 5 (Icc 0.15 0.20 ∪ Icc 0.80 0.85) ≤ 0.572090 := by
  have hl := checkLowerSixSlices_sound (a := 150000) (b := 200000)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    Native.dm1520_interior1_checked Native.dm1520_interior2_checked Native.dm1520_interior3_checked
    Native.dm1520_tail1_checked Native.dm1520_tail2_checked Native.dm1520_tail3_checked
  have h := checked_window_bounds hl Native.dm1520_upper_checked
  rw [denote_symmetricWindow (by decide) (by decide)] at h
  norm_num [grid, lowerSliceRound, quotient, unit] at h ⊢
  exact h

end LeastPrime

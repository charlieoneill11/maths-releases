import LeastPrime.Native.Tin
import LeastPrime.Native.Tout

/-! The two unconditional bounds in Proposition 14. -/

namespace LeastPrime

open Checker

theorem p6_Tin : P6Tin := by
  have h := checkWindow_sound Native.tin_checked
  rw [denote_symmetricWindow_tin] at h
  change grid 587142 ≤ (stickLaw 6).real (E 6 Tin) at h
  change 0.587142 ≤ (stickLaw 6).real (E 6 Tin)
  simpa only [show grid 587142 = (0.587142 : ℝ) by norm_num [grid, unit]] using h

theorem q5_Tout : Q5Tout := by
  have h := checkWindow_sound Native.tout_checked
  rw [denote_symmetricWindow_tout] at h
  change (stickLaw 5).real (F 5 Tout) ≤ grid 595573 at h
  change (stickLaw 5).real (F 5 Tout) ≤ 0.595573
  simpa only [show grid 595573 = (0.595573 : ℝ) by norm_num [grid, unit]] using h

end LeastPrime

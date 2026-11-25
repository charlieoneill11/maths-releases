import LeastPrime.Checker.Sound
import LeastPrime.Checker.Windows

/-! Soundness of a Boolean certificate for one symmetric grid window. -/

namespace LeastPrime.Checker

theorem checkWindow_sound {bound : Bound} {k a b expected : ℕ}
    (h : checkWindow bound k a b expected = true) :
    Bounds bound (grid expected) (probabilityFor bound k (denote (symmetricWindow a b))) := by
  simp only [checkWindow, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simpa only [h.2] using probabilityBound_sound bound k (symmetricWindow a b)
    (valid_symmetricWindow h.1.1 h.1.2)

end LeastPrime.Checker

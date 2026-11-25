import HadwigerNelson.Stars.Partition
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith

/-! Transfer local inequalities through the actual dyadic angular traversal. -/

namespace HadwigerNelson.Stars.BoxCheck

theorem leafEval_lower (src : Angular.Box) (other q : Nat) (G : Nat → ℝ) (f : Span → ℝ)
    (bound : ∀ a b, a < b → b ≤ resolution → f (nodeSpan src other q a b) ≤ G b-G a)
    (d a : Nat) (stop : a+2^d ≤ resolution) :
    leafEval src other q f d a ≤ G (a+2^d)-G a := by
  induction d generalizing a with
  | zero => simpa [leafEval] using bound a (a+1) (by omega) (by simpa using stop)
  | succ d ih =>
    have pos : 0 < 2^d := Nat.two_pow_pos _
    have endid : a+2^d+2^d = a+2^(d+1) := by rw [Nat.pow_succ]; omega
    rw [leafEval]
    split
    · exact bound _ _ (by omega) stop
    · have h1 := ih a (by omega)
      have h2 := ih (a+2^d) (by omega)
      rw [endid] at h2
      linarith

/-- The absolute errors of the realized primitive relative to its signed
step approximation add over leaves, including every uncertainty radius. -/
theorem leafEval_error {B : Type*} [SeminormedAddCommGroup B]
    (src : Angular.Box) (other q : Nat) (G : Nat → B) (f : Span → B) (err : Span → ℝ)
    (bound : ∀ a b, a < b → b ≤ resolution →
      ‖G b-G a-f (nodeSpan src other q a b)‖ ≤ err (nodeSpan src other q a b))
    (d a : Nat) (stop : a+2^d ≤ resolution) :
    ‖G (a+2^d)-G a-leafEval src other q f d a‖ ≤ leafEval src other q err d a := by
  induction d generalizing a with
  | zero => simpa [leafEval] using bound a (a+1) (by omega) (by simpa using stop)
  | succ d ih =>
    have pos : 0 < 2^d := Nat.two_pow_pos _
    have endid : a+2^d+2^d = a+2^(d+1) := by rw [Nat.pow_succ]; omega
    rw [leafEval,leafEval]
    split
    · exact bound _ _ (by omega) stop
    · have h1 := ih a (by omega)
      have h2 := ih (a+2^d) (by omega)
      rw [endid] at h2
      calc
        _ = ‖(G (a+2^d)-G a-leafEval src other q f d a) +
            (G (a+2^(d+1))-G (a+2^d)-leafEval src other q f d (a+2^d))‖ := by
          congr 1
          abel
        _ ≤ _ := (norm_add_le _ _).trans (add_le_add h1 h2)

end HadwigerNelson.Stars.BoxCheck

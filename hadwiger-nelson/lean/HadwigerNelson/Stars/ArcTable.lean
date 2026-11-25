import HadwigerNelson.Stars.MomentsRuntime
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Prefix subtraction preserves the lower and upper sums of the individual
angular increments. The lower/lower and upper/upper differences use the
same sequence of increments at both endpoints. -/

namespace HadwigerNelson.Stars.BoxCheck

theorem arcPrefix_succ (n : Nat) :
    arcPrefix (n+1) =
    let s := arcPrefix n
    let a : Arc := ⟨s.1.low+(arcStep n).low,s.1.high+(arcStep n).high⟩
    (a,s.2.push a) := rfl

theorem arcPrefix_size (n : Nat) : (arcPrefix n).2.size = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [arcPrefix_succ,ih]

theorem arcPrefix_get (i n : Nat) (hi : i ≤ n) :
    (arcPrefix n).2[i]? = some (arcPrefix i).1 := by
  induction n with
  | zero =>
    obtain rfl : i = 0 := by omega
    rfl
  | succ n ih =>
    rw [arcPrefix_succ]
    by_cases eq : i = n+1
    · subst i
      conv_lhs => rw [← arcPrefix_size n]
      rw [Array.getElem?_push_size,arcPrefix_succ]
    · have idx : i < (arcPrefix n).2.size := by rw [arcPrefix_size]; omega
      rw [Array.getElem?_push_lt idx, ← Array.getElem?_eq_getElem idx]
      exact ih (by omega)

theorem spanArc_bounds (angle : Nat → ℝ)
    (step : ∀ i, ((arcStep i).low : ℝ) ≤ angle (i+1)-angle i ∧
             angle (i+1)-angle i ≤ (arcStep i).high)
    (s : Span) (hle : s.start ≤ s.stop) (hhi : s.stop ≤ resolution) :
    ((spanArc arcTable s).low : ℝ) ≤ angle s.stop-angle s.start ∧
    angle s.stop-angle s.start ≤ (spanArc arcTable s).high := by
  have interval (i j : Nat) (h : i ≤ j) :
      ((arcPrefix j).1.low : ℝ)-(arcPrefix i).1.low ≤ angle j-angle i ∧
      angle j-angle i ≤ ((arcPrefix j).1.high : ℝ)-(arcPrefix i).1.high := by
    induction j with
    | zero =>
      obtain rfl : i = 0 := by omega
      simp
    | succ j ih =>
      by_cases e : i = j+1
      · subst i; simp
      obtain ⟨prev₁,prev₂⟩ := ih (by omega)
      have ⟨lo,hi⟩ := step j
      rw [arcPrefix_succ]
      push_cast
      constructor <;> linarith
  simpa only [spanArc,arcTable,arcPrefix_get s.start resolution (hle.trans hhi),
    arcPrefix_get s.stop resolution hhi,Option.getD_some,Int.cast_sub] using
    interval s.start s.stop hle

end HadwigerNelson.Stars.BoxCheck

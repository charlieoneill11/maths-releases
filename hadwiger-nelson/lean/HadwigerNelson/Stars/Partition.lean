import HadwigerNelson.Stars.BoxRuntime
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Abel

/-! Every dyadic leaf is visited in increasing angular order. Merging adjacent
spans with the same signed midpoint and radius preserves all additive endpoint
increments, which include realized integrals, signed means, and Fourier moments. -/

namespace HadwigerNelson.Stars.BoxCheck

variable {A : Type*} [AddCommGroup A]

/-- An arbitrary primitive function for each quadrant and signed envelope. -/
def changeOf (F : Nat → Int → Int → Nat → A) (s : Span) : A :=
  F s.quadrant s.coeff s.radius s.stop - F s.quadrant s.coeff s.radius s.start

def spanEval (ss : Array Span) (f : Span → A) := (ss.toList.map f).sum

theorem spanEval_append (ss : Array Span) (s : Span) (F : Nat → Int → Int → Nat → A) :
    spanEval (appendSpan ss s) (changeOf F) = spanEval ss (changeOf F) + changeOf F s := by
  by_cases empty : ss = #[]
  · simp [empty,spanEval,appendSpan]
  · obtain ⟨xs,p,rfl⟩ := Array.exists_push_of_ne_empty empty
    simp only [appendSpan, Array.back?_push]
    split
    · rename_i h
      simp only [Bool.and_eq_true,beq_iff_eq] at h
      obtain ⟨⟨⟨q,e⟩,c⟩,r⟩ := h
      simp [spanEval,changeOf,q,e,c,r]
      abel
    · simp [spanEval,add_assoc]

def nodeSpan (source : Angular.Box) (other q a stop : Nat) : Span :=
  let b := destination source (quadrant q (Angular.halfAngleBox resolution a stop))
  let pair := signedStep (classify b 1) (classify b other)
  ⟨q,a,stop,pair.1,pair.2⟩

/-- Subdivision tree with the same stopping rules as the checker. It uses
no accumulator and expresses its result as a sum of the unmerged leaves. -/
def leafEval (source : Angular.Box) (other q : Nat) (f : Span → A) : Nat → Nat → A
  | 0, a => f (nodeSpan source other q a (a+1))
  | d+1, a =>
    let s := nodeSpan source other q a (a+2^(d+1))
    if s.radius == 0 then f s
    else leafEval source other q f d a + leafEval source other q f d (a+2^d)

theorem traverse_eval (source : Angular.Box) (other q : Nat) (F : Nat → Int → Int → Nat → A)
    (d a : Nat) (out : Array Span) :
    spanEval (traverse source other q d a out) (changeOf F) =
    spanEval out (changeOf F) + leafEval source other q (changeOf F) d a := by
  induction d generalizing a out with
  | zero =>
    simp only [traverse,leafEval,nodeSpan,spanEval_append]
  | succ d ih =>
    simp only [traverse,leafEval,nodeSpan]
    split
    · exact spanEval_append .. 
    · rw [ih,ih,add_assoc]

theorem runs_eval (source : Angular.Box) (other : Nat) (F : Nat → Int → Int → Nat → A) :
    spanEval (runs source other) (changeOf F) =
      leafEval source other 0 (changeOf F) 17 0 + leafEval source other 1 (changeOf F) 17 0 +
      leafEval source other 2 (changeOf F) 17 0 + leafEval source other 3 (changeOf F) 17 0 := by
  change spanEval (traverse source other 3 17 0 (traverse source other 2 17 0
    (traverse source other 1 17 0 (traverse source other 0 17 0 #[])))) (changeOf F) = _
  rw [traverse_eval,traverse_eval,traverse_eval,traverse_eval]
  simp [spanEval]

end HadwigerNelson.Stars.BoxCheck

import HadwigerNelson.Stars.Partial.Runtime
import HadwigerNelson.Stars.Partition

/-! Additive endpoint differences telescope across a merged partial-wave span.
Zero steps are omitted by the executable and contribute zero to the moments. -/

namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (Span spanEval changeOf appendSpan spanEval_append)

variable {B : Type*} [AddCommGroup B]

def treeEval (src : Angular.Box) (other q : Nat) (f : Span → B) : Nat → Nat → B
  | 0, a => f ⟨q,a,a+1,(node src other q a (a+1)).1,0⟩
  | d+1,a =>
    let p := node src other q a (a+2^(d+1))
    if p.2 then f ⟨q,a,a+2^(d+1),p.1,0⟩
    else treeEval src other q f d a + treeEval src other q f d (a+2^d)

private theorem emit (F : Nat → Int → Int → Nat → B) (empty : ∀ q i, F q 0 0 i=0)
    (out : Array Span) (q a b : Nat) (s : Int) :
    spanEval (if s==0 then out else appendSpan out ⟨q,a,b,s,0⟩) (changeOf F) =
      spanEval out (changeOf F) + changeOf F ⟨q,a,b,s,0⟩ := by
  by_cases eq : s=0
  · simp [eq,changeOf,empty]
  · simpa only [beq_iff_eq,eq,if_false] using spanEval_append out ⟨q,a,b,s,0⟩ F

theorem visit_eval (src : Angular.Box) (other q : Nat) (F : Nat → Int → Int → Nat → B)
    (empty : ∀ q i, F q 0 0 i=0) (d a : Nat) (out : Array Span) :
    spanEval (visit src other q d a out) (changeOf F) =
      spanEval out (changeOf F) + treeEval src other q (changeOf F) d a := by
  induction d generalizing a out with
  | zero => exact emit F empty out _ _ _ _
  | succ d ih =>
    by_cases fixed : (node src other q a (a+2^(d+1))).2
    · simp only [visit,treeEval,fixed,if_true]
      exact emit F empty out _ _ _ _
    · simp only [visit,treeEval,fixed,Bool.false_eq_true,if_false]
      rw [ih,ih,add_assoc]

theorem runs_eval (src : Angular.Box) (other : Nat) (F : Nat → Int → Int → Nat → B)
    (empty : ∀ q i, F q 0 0 i=0) :
    spanEval (runs src other) (changeOf F) =
      treeEval src other 0 (changeOf F) 17 0 + treeEval src other 1 (changeOf F) 17 0 +
      treeEval src other 2 (changeOf F) 17 0 + treeEval src other 3 (changeOf F) 17 0 := by
  change spanEval (visit src other 3 17 0 (visit src other 2 17 0
    (visit src other 1 17 0 (visit src other 0 17 0 #[])))) _ = _
  rw [visit_eval _ _ _ _ empty,visit_eval _ _ _ _ empty,visit_eval _ _ _ _ empty,visit_eval _ _ _ _ empty]
  simp [spanEval]

end HadwigerNelson.Stars.PartialCheck

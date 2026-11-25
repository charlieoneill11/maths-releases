import HadwigerNelson.Stars.Partial.Runtime
import Mathlib.Data.Nat.Basic

namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (Span appendSpan resolution)

def ValidSpan (p : Span) : Prop :=
  p.quadrant<4 ∧ p.start≤p.stop ∧ p.stop≤resolution ∧ (p.coeff = -1 ∨ p.coeff = 1)

private theorem emit_valid (ss : Array Span) (valid : ∀p∈ss, ValidSpan p) (s : Span) (hs : ValidSpan s) :
    ∀ p∈appendSpan ss s, ValidSpan p := by
  obtain none|⟨last,some⟩ := Option.eq_none_or_eq_some (ss.back?)
  · simpa only [appendSpan,none,Array.forall_mem_singleton] using hs
  obtain ⟨previous,rfl⟩ := Array.back?_eq_some_iff.mp some
  simp only [appendSpan,Array.back?_push]
  split
  · rename_i join
    simp only [Bool.and_eq_true,beq_iff_eq] at join
    obtain ⟨⟨⟨q,endstart⟩,coeff⟩,rad⟩ := join
    obtain ⟨hq,ordered,_,sign⟩ := valid last (by simp)
    simp only [Array.pop_push,Array.mem_push]
    rintro p (pold|rfl)
    · exact valid p (by simp [pold])
    · exact ⟨hq,Nat.le_trans ordered (endstart ▸ hs.2.1),hs.2.2.1,sign⟩
  · intro p mem
    rcases Array.mem_push.mp mem with pold|rfl
    · exact valid p pold
    · exact hs

theorem visit_valid (src : Angular.Box) (other q : Nat) (hq : q<4) (d a : Nat) (ha : a+2^d≤resolution)
    (out : Array Span) (valid : ∀p∈out, ValidSpan p) : ∀ p∈visit src other q d a out, ValidSpan p := by
  have signs (i j : Nat) : (node src other q i j).1 = -1 ∨
      (node src other q i j).1 = 0 ∨ (node src other q i j).1 = 1 := by
    have h (n m : BoxCheck.Status) : (lowerStep n m).1 = -1 ∨ (lowerStep n m).1 = 0 ∨ (lowerStep n m).1 = 1 := by
      cases n <;> cases m <;> decide
    exact h _ _
  have emit (i j : Nat) (ij : i≤j) (stop : j≤resolution) (s : Array Span) (v : ∀p∈s,ValidSpan p) :
      ∀p∈(if (node src other q i j).1==0 then s else appendSpan s ⟨q,i,j,(node src other q i j).1,0⟩),ValidSpan p := by
    split
    · exact v
    · rename_i nonzero
      have nz : (node src other q i j).1 ≠ 0 := by
        intro eq
        simp [eq] at nonzero
      exact emit_valid _ v _ ⟨hq,ij,stop,(signs i j).imp_right (fun h => h.resolve_left nz)⟩
  induction d generalizing a out with
  | zero => exact emit a (a+1) (by omega) ha out valid
  | succ d ih =>
    have eq : a+2^d+2^d = a+2^(d+1) := by rw [Nat.pow_succ];omega
    by_cases fixed : (node src other q a (a+2^(d+1))).2
    · simp only [visit,fixed,if_true]
      exact emit _ _ (Nat.le_add_right ..) ha out valid
    · simp only [visit,fixed,Bool.false_eq_true,if_false]
      exact ih _ (eq ▸ ha) _ (ih a (Nat.le_trans (Nat.le_add_right _ _) (eq ▸ ha)) _ valid)

theorem runs_valid (src : Angular.Box) (other : Nat) : ∀ p∈runs src other, ValidSpan p := by
  unfold runs
  apply visit_valid _ _ _ (by decide) 17 0 (by decide)
  apply visit_valid _ _ _ (by decide) 17 0 (by decide)
  apply visit_valid _ _ _ (by decide) 17 0 (by decide)
  apply visit_valid _ _ _ (by decide) 17 0 (by decide)
  simp

end HadwigerNelson.Stars.PartialCheck

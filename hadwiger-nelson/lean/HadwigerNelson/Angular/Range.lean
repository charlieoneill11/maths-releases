import HadwigerNelson.Angular.Bins
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals

namespace HadwigerNelson.Angular
open scoped BigOperators

private theorem go_eq (f : Nat → Nat) (n start acc : Nat) :
    rangeSum.go f start n acc = acc + ∑ j ∈ Finset.range n, f (start+j) := by
  induction n generalizing start acc with
  | zero => simp [rangeSum.go]
  | succ n ih =>
    rw [rangeSum.go,ih,Finset.sum_range_succ']
    simp only [Nat.add_zero]
    have h : (∑ i ∈ Finset.range n, f (start+1+i)) =
        ∑ i ∈ Finset.range n, f (start+(i+1)) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega
    rw [h]
    omega

theorem rangeSum_spec (f : Nat → Nat) (start n : Nat) :
    rangeSum f start n = ∑ j ∈ Finset.range n, f (start+j) := by
  simp [rangeSum, go_eq]

theorem rangeSum_split (f : Nat → Nat) (start a b : Nat) :
    rangeSum f start (a+b) = rangeSum f start a + rangeSum f (start+a) b := by
  simp only [rangeSum_spec, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  omega

theorem rangeSum_le_of_group_bounds (f : Nat → Nat) (groups chunk : Nat)
    (bounds : Nat → Nat)
    (h : ∀ k < groups, rangeSum f (k*chunk) chunk ≤ bounds k) :
    rangeSum f 0 (groups*chunk) ≤ ∑ k ∈ Finset.range groups, bounds k := by
  induction groups with
  | zero => simp [rangeSum_spec]
  | succ n ih =>
    rw [Nat.succ_mul,rangeSum_split,zero_add,Finset.sum_range_succ]
    exact Nat.add_le_add (ih (fun k hk => h k (by omega))) (h n (by omega))

end HadwigerNelson.Angular

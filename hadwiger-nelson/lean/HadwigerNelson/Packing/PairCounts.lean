import HadwigerNelson.Packing.Parameters
import HadwigerNelson.Crossings.Subsets
import Mathlib.Data.Nat.Choose.Basic

namespace HadwigerNelson.Packing
open Finset
noncomputable section

def closeNeighbours (B : Finset Plane) (x : Plane) (d : ℝ) : Finset Plane := by
  classical exact B.filter fun y ↦ x ≠ y ∧ dist x y < d

def between (A B : Finset Plane) (d : ℝ) : ℕ := ∑ x ∈ A, (closeNeighbours B x d).card

theorem between_symm (A B : Finset Plane) (d : ℝ) : between A B d = between B A d := by
  classical
  unfold between closeNeighbours
  rw [Crossings.sum_filter_card]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  ext x
  simp only [Finset.mem_filter,ne_comm (a:=x) (b:=y),dist_comm x y]

theorem between_union (A B C : Finset Plane) (d : ℝ) (dis : Disjoint A B) :
    between (A ∪ B) C d = between A C d + between B C d := by
  classical exact Finset.sum_union dis

theorem between_partition (A B : Finset Plane) (d : ℝ) (h : B ⊆ A) :
    between A A d = between (A \ B) (A \ B) d + 2*between (A \ B) B d + between B B d := by
  classical
  let U := A \ B
  have decomp (T) : between A T d = between U T d + between B T d := by
    conv_lhs => rw [← Finset.sdiff_union_of_subset h]
    exact between_union U B T d Finset.sdiff_disjoint
  rw [decomp,between_symm U A,decomp U,between_symm B A,decomp B,between_symm B U]
  dsimp only [U]
  omega

theorem between_add (A B C : Finset Plane) (d : ℝ) (dis : Disjoint A B) :
    between C (A ∪ B) d = between C A d + between C B d := by
  rw [between_symm C,between_union A B C d dis,between_symm A C,between_symm B C]

theorem between_bound (A B : Finset Plane) (d : ℝ) (k : ℕ)
    (h : ∀ x ∈ A, (closeNeighbours B x d).card ≤ k) : between A B d ≤ A.card*k := by
  unfold between
  simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum h

theorem between_self_bound (A : Finset Plane) (d : ℝ) : between A A d ≤ 2*A.card.choose 2 := by
  classical
  have bound := between_bound A A d (A.card-1) (by
    intro x hx
    rw [← Finset.card_erase_of_mem hx]
    apply Finset.card_le_card
    intro y hy
    obtain ⟨yA,ne,_⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_erase.mpr ⟨ne.symm,yA⟩)
  have eq := Nat.descFactorial_eq_factorial_mul_choose A.card 2
  rw [Nat.factorial_two] at eq
  simpa [←eq,Nat.descFactorial_succ,Nat.mul_comm] using bound

theorem between_self_zero (A : Finset Plane) {d : ℝ} (sep : separated A d) : between A A d = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨yA,ne,near⟩ := Finset.mem_filter.mp hy
  exact (sep x hx y yA ne).not_gt near

end
end HadwigerNelson.Packing

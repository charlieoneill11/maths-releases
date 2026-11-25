import Shumyatsky.Paths

namespace Shumyatsky.Cycle
open Equiv Equiv.Perm
variable {ι A O : Type*} [Group A] [Group O]

noncomputable def anchor (σ : Perm ι) (i : ι) : ι :=
  (Quotient.mk (SameCycle.setoid σ) i).out

theorem anchor_eq {σ : Perm ι} {i j : ι} (h : σ.SameCycle i j) :
    anchor σ i = anchor σ j :=
  congrArg Quotient.out (Quotient.sound (s := SameCycle.setoid σ) h)

theorem anchor_cycle (σ : Perm ι) (i : ι) : σ.SameCycle (anchor σ i) i :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (SameCycle.setoid σ) i))

theorem anchor_next (σ : Perm ι) (i : ι) : anchor σ (σ i) = anchor σ i :=
  anchor_eq ((SameCycle.refl σ i).apply_left)

variable [Finite ι]

open scoped Classical in
noncomputable def distance (σ : Perm ι) (i : ι) : ℕ :=
  Nat.find (anchor_cycle σ i).exists_nat_pow_eq

theorem distance_spec (σ : Perm ι) (i : ι) : (σ ^ distance σ i) (anchor σ i) = i := by
  classical
  exact Nat.find_spec (anchor_cycle σ i).exists_nat_pow_eq

theorem distance_le (σ : Perm ι) (i : ι) {n : ℕ} (h : (σ ^ n) (anchor σ i) = i) :
    distance σ i ≤ n := by
  classical
  exact Nat.find_min' (anchor_cycle σ i).exists_nat_pow_eq h

/-- The reserved edge enters the chosen anchor. Every other edge increases
the forward distance from that anchor by one. -/
def free (σ : Perm ι) (i : ι) : Prop := σ i ≠ anchor σ i

omit [Finite ι] in
theorem free_unique (σ : Perm ι) (i j : ι) (hi : ¬free σ i) (hj : ¬free σ j)
    (h : σ.SameCycle i j) : i = j := by
  classical
  apply σ.injective
  exact (not_ne_iff.mp hi).trans ((anchor_eq h).trans (not_ne_iff.mp hj).symm)

theorem distance_succ (σ : Perm ι) (i : ι) (hi : free σ i) :
    distance σ (σ i) = distance σ i + 1 := by
  apply Nat.le_antisymm
  · apply distance_le
    rw [anchor_next, pow_succ', Equiv.Perm.mul_apply, distance_spec]
  · have h := distance_spec σ (σ i)
    rw [anchor_next] at h
    cases hn : distance σ (σ i) with
    | zero =>
      rw [hn, pow_zero] at h
      exact (hi h.symm).elim
    | succ n =>
      rw [hn, pow_succ', Equiv.Perm.mul_apply] at h
      exact Nat.succ_le_succ (distance_le σ i (σ.injective h))

private def run (σ : Perm ι) (x y g₀ : ι → A) (s : ι) : ℕ → A
  | 0 => g₀ s
  | n + 1 => y ((σ ^ n) s) * run σ x y g₀ s n * (x ((σ ^ n) s))⁻¹

/-- Here the y-labels are indexed by the corresponding x-source (pullback
along the permutation of the conjugator). All free labels are realized at once. -/
theorem reconstruct (σ : Perm ι) (q : A →* O) (x y g₀ : ι → A)
    (outer : ∀ i, q (g₀ (σ i)) * q (x i) = q (y i) * q (g₀ i)) :
    ∃ g z : ι → A, (∀ i, q (g i) = q (g₀ i)) ∧ (∀ i, q (z i) = q (y i)) ∧
      (∀ i, free σ i → z i = y i) ∧ ∀ i, g (σ i) * x i = z i * g i := by
  let g i := run σ x y g₀ (anchor σ i) (distance σ i)
  have proj (s : ι) (n : ℕ) : q (run σ x y g₀ s n) = q (g₀ ((σ ^ n) s)) := by
    induction n with
    | zero => simp [run]
    | succ n ih =>
      rw [run, map_mul, map_mul, map_inv, ih, ← outer, mul_inv_cancel_right,
        pow_succ', Equiv.Perm.mul_apply]
  have hg (i : ι) : q (g i) = q (g₀ i) := by
    simpa [g, distance_spec] using proj (anchor σ i) (distance σ i)
  refine ⟨g, fun i => g (σ i) * x i * (g i)⁻¹, hg, ?_, ?_, fun i => by group⟩
  · intro i
    rw [map_mul, map_mul, map_inv, hg, hg, outer]
    group
  · intro i hi
    have h : g (σ i) = y i * g i * (x i)⁻¹ := by
      simp only [g, distance_succ σ i hi, anchor_next, run, distance_spec]
    change g (σ i) * x i * (g i)⁻¹ = y i
    rw [h]
    group

end Shumyatsky.Cycle

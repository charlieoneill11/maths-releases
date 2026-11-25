import Shumyatsky.Labels
import Mathlib.GroupTheory.Perm.Cycle.Basic

namespace Shumyatsky
open Equiv Equiv.Perm

variable {ι A : Type*} [Group A]

/-- A word in forward and inverse edges, recording its restriction at the source. -/
inductive Walk (σ τ : Perm ι) (x y : ι → A) (X Y : ι → Prop) : ι → ι → A → Prop
  | refl (i) : Walk σ τ x y X Y i i 1
  | first {i} : X i → Walk σ τ x y X Y i (σ i) (x i)
  | second {i} : Y i → Walk σ τ x y X Y i (τ i) (y i)
  | rev {i j a} : Walk σ τ x y X Y i j a → Walk σ τ x y X Y j i a⁻¹
  | comp {i j k a b} : Walk σ τ x y X Y i j a → Walk σ τ x y X Y j k b →
      Walk σ τ x y X Y i k (b * a)

namespace Walk

theorem transfer {σ τ : Perm ι} {x y x' y' : ι → A} {X Y : ι → Prop}
    (hx : ∀ i, X i → x' i = x i) (hy : ∀ i, Y i → y' i = y i)
    {i j a} (w : Walk σ τ x y X Y i j a) :
    Walk σ τ x' y' (fun _ => True) (fun _ => True) i j a := by
  induction w with
  | refl => exact .refl _
  | first h => rw [← hx _ h]; exact .first trivial
  | second h => rw [← hy _ h]; exact .second trivial
  | rev _ ih => exact .rev ih
  | comp _ _ ih jh => exact .comp ih jh

def connectedBy (σ τ : Perm ι) : Prop :=
  ∀ (r : Setoid ι), (∀ i, r.r i (σ i)) → (∀ i, r.r i (τ i)) → ∀ i j, r.r i j

/-- After deleting at most one source per cycle, equivalence along the retained
edges still implies equivalence across every omitted edge. -/
theorem reconnect [Finite ι] (σ : Perm ι) (r : Setoid ι) (keep : ι → Prop)
    (oneCut : ∀ i j, ¬keep i → ¬keep j → σ.SameCycle i j → i = j)
    (step : ∀ i, keep i → r.r i (σ i)) (i : ι) : r.r i (σ i) := by
  classical
  by_cases h : keep i
  · exact step i h
  have path (n : ℕ) : r.r (σ i) ((σ ^ n) (σ i)) := by
    induction n with
    | zero => rw [pow_zero]; exact r.iseqv.refl _
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      by_cases hn : keep ((σ ^ n) (σ i))
      · exact r.trans ih (step _ hn)
      · have he := oneCut i _ h hn ((SameCycle.refl σ i).apply_right.pow_right)
        rw [← he]

  obtain ⟨n, hn⟩ := ((SameCycle.refl σ i).apply_left).exists_nat_pow_eq
  have hp := path n
  rw [hn] at hp
  exact r.symm hp

def relation (σ τ : Perm ι) (x y : ι → A) (X Y : ι → Prop) : Setoid ι where
  r i j := ∃ a, Walk σ τ x y X Y i j a
  iseqv := ⟨fun i => ⟨_, .refl i⟩, fun ⟨a,w⟩ => ⟨a⁻¹, .rev w⟩,
    fun ⟨a,w⟩ ⟨b,v⟩ => ⟨b * a, .comp w v⟩⟩

theorem retained_paths [Finite ι] {σ τ : Perm ι} (h : connectedBy σ τ)
    (x y : ι → A) (X Y : ι → Prop)
    (hX : ∀ i j, ¬X i → ¬X j → σ.SameCycle i j → i = j)
    (hY : ∀ i j, ¬Y i → ¬Y j → τ.SameCycle i j → i = j) (i j : ι) :
    ∃ a, Walk σ τ x y X Y i j a :=
  h (relation σ τ x y X Y)
    (reconnect σ _ X hX (fun _ hi => ⟨_, .first hi⟩))
    (reconnect τ _ Y hY (fun _ hi => ⟨_, .second hi⟩)) i j

theorem one_cycle_paths [Finite ι] {σ τ : Perm ι} (h : ∀ i j, σ.SameCycle i j)
    (x y : ι → A) (root i j : ι) :
    ∃ a, Walk σ τ x y (· ≠ root) (fun _ => False) i j a := by
  classical
  let r := relation σ τ x y (· ≠ root) (fun _ => False)
  have step := reconnect σ r (· ≠ root) (fun a b ha hb _ =>
    (not_ne_iff.mp ha).trans (not_ne_iff.mp hb).symm) (fun _ hi => ⟨_, .first hi⟩)
  obtain ⟨n, rfl⟩ := (h i j).exists_nat_pow_eq
  induction n with
  | zero => rw [pow_zero]; exact r.iseqv.refl _
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact r.trans ih (step _)

end Walk
end Shumyatsky

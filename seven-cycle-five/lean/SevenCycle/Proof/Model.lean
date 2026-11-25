import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card

/-!
The proof works with product codes for a coordinate relation. Specialising
that relation to a single cycle step gives the public definitions by reduction.
Keeping this module below the public statement lets the proofs be developed
without importing either of the main theorems.
-/
namespace SevenCycle.Proof

abbrev Tuple (n : ℕ) := Fin n → ZMod 7

def cycleStep (a b : ZMod 7) : Prop := a - b ∈ ({-1, 0, 1} : Finset (ZMod 7))

def conflict {α : Type*} {n : ℕ} (near : α → α → Prop) (x y : Fin n → α) : Prop :=
  x ≠ y ∧ ∀ i, near (x i) (y i)

def packing {α : Type*} {n : ℕ} (near : α → α → Prop) (C : Finset (Fin n → α)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ¬ conflict near x y

end SevenCycle.Proof

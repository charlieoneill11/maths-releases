import SevenCycle.Atlas.Invariants
import SevenCycle.Bitsets.Orbit
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace SevenCycle.Atlas.Stabilizers

open Proof Blueprint

private def enumSum (n : ℕ) (f : Fin n → ℕ) : ℕ :=
  Invariants.sumN (fun i => if h : i < n then f ⟨i,h⟩ else 0) n

private theorem enumSum_eq {n : ℕ} (f : Fin n → ℕ) : enumSum n f = ∑ i, f i := by
  simp [enumSum, Invariants.sumN_eq]

private noncomputable def permEquiv : Fin 6 ≃ Equiv.Perm (Fin 3) :=
  Equiv.ofBijective Bitsets.perm3 ⟨by
    have : ∀ i j : Fin 6, Bitsets.perm3 i = Bitsets.perm3 j → i = j := by decide
    exact fun _ _ => this _ _, Bitsets.perm3_surjective⟩

private noncomputable def signEquiv : Fin 8 ≃ (Fin 3 → Bool) :=
  Equiv.ofBijective Bitsets.sign3 ⟨by
    have : ∀ i j : Fin 8, Bitsets.sign3 i = Bitsets.sign3 j → i = j := by decide
    exact fun _ _ => this _ _, Bitsets.sign3_surjective⟩

private def tupleEquiv : (Fin 7 × Fin 7 × Fin 7) ≃ Tuple 3 where
  toFun u := ![u.1, u.2.1, u.2.2]
  invFun w := (w 0, w 1, w 2)
  left_inv _ := rfl
  right_inv w := by funext i; fin_cases i <;> rfl

private def preserves (r : Vector UInt64 7) (a : Array (Tuple 3)) (g : Isometry 3) : Bool :=
  a.all fun x => hasWord r (act g x)

private theorem preserves_iff (r : Vector UInt64 7) (g : Isometry 3) :
    preserves r (decodedWords r) g = true ↔ actOnCode g (decodedSet r) = decodedSet r := by
  have memD (w : Tuple 3) : w ∈ decodedWords r ↔ w ∈ decodedSet r := by
    rw [← decodedWords_set, rowSet, Finset.mem_image]
    simp only [Finset.mem_univ, true_and]
    exact ⟨fun h => by obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.mp h; exact ⟨⟨i,hi⟩, e⟩,
      fun ⟨i,e⟩ => Array.mem_iff_getElem.mpr ⟨i.val,i.isLt,e⟩⟩
  have ma (w : Tuple 3) : hasWord r w = true ↔ w ∈ decodedSet r := by simp [decodedSet]
  have hi : Function.Injective (act g) := fun _ _ e => by
    simpa only [Symmetry.undo_act] using congrArg (act (Symmetry.undo g)) e
  rw [preserves, Array.all_eq_true_iff_forall_mem]
  constructor
  · intro h
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
      exact (ma _).1 (h _ ((memD _).2 hx))
    · simp [actOnCode, Finset.card_image_of_injective _ hi]
  · intro eq x hx
    apply (ma _).2
    rw [← eq]
    exact Finset.mem_image_of_mem _ ((memD _).1 hx)

/-- Test the 48 signed permutations and the translations independently in each axis. -/
def stabilizers (r : Vector UInt64 7) : ℕ :=
  let a := decodedWords r
  enumSum 6 fun p => enumSum 8 fun s =>
    enumSum 7 fun i => enumSum 7 fun j => enumSum 7 fun k =>
      if preserves r a (Bitsets.perm3 p, Bitsets.sign3 s, ![i,j,k]) then 1 else 0

private theorem mapSum (f : Isometry 3 → ℕ) :
    (∑ g, f g) = ∑ p : Fin 6, ∑ s : Fin 8, ∑ i : Fin 7, ∑ j : Fin 7, ∑ k : Fin 7,
      f (Bitsets.perm3 p, Bitsets.sign3 s, ![i,j,k]) := by
  let e := permEquiv.prodCongr (signEquiv.prodCongr tupleEquiv)
  have h := Equiv.sum_comp e f
  simpa only [Fintype.sum_prod_type, e, Equiv.prodCongr_apply, permEquiv, signEquiv,
    Equiv.ofBijective_apply, tupleEquiv] using h.symm

private theorem cardBySum {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ i, (if p i then 1 else 0 : ℕ) := by
  simpa only [Nat.cast_id] using (Finset.sum_boole (R := ℕ) p Finset.univ).symm

theorem stabilizers_eq (i : Fin atlasPlanes.size) :
    stabilizers atlasPlanes[i] = stabilizerOrder i := by
  classical
  rw [stabilizerOrder, cardBySum, mapSum]
  simp only [stabilizers, enumSum_eq, preserves_iff]
  rfl

/-- Candidate stabiliser orders indexed from zero. Each value is checked against every group element. -/
def orderHint (i : ℕ) : ℕ :=
  if i = 501 ∨ i = 932 ∨ i = 936 then 3
  else if i = 903 then 2
  else if i = 986 then 6
  else 1

structure Block where
  rows : Array (Vector UInt64 7)
  start : ℕ
  size : ℕ

def blockCheck (b : Block) : Bool :=
  (Array.range b.size).all fun j =>
    let i := b.start + j
    if h : i < b.rows.size then stabilizers b.rows[i] == orderHint i else false

theorem blockCheck_sound (b : Block) (ok : blockCheck b = true) (i : Fin b.rows.size)
    (lo : b.start ≤ i.val) (hi : i.val < b.start + b.size) :
    stabilizers b.rows[i] = orderHint i.val := by
  have hj : i.val - b.start ∈ Array.range b.size := Array.mem_range.mpr (by omega)
  have h := Array.all_eq_true'.mp ok _ hj
  have e : b.start + (i.val - b.start) = i.val := by omega
  simpa only [e, i.isLt, dite_true, beq_iff_eq] using h

theorem hint_histogram : let count := fun j : ℕ =>
    (Finset.univ.filter (fun i : Fin 1016 => orderHint i.val = j)).card
    count 1 = 1011 ∧ count 2 = 1 ∧ count 3 = 3 ∧ count 6 = 1 := by
  decide +kernel

end SevenCycle.Atlas.Stabilizers

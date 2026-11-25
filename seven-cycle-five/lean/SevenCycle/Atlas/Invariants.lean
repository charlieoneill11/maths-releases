import SevenCycle.Atlas.Rows
import SevenCycle.Proof.Symmetry
import Mathlib.Algebra.BigOperators.Fin

/-!
# Separating the released orbits

For each pair of words assign the weight (∑ₖ 4^distanceₖ)². Sum these weights
at each word, square the resulting sum, and add over all words. Each operation
is invariant under signed affine permutations. Although this statistic need
not classify arbitrary codes, its 1,016 values on the released rows are distinct.
-/

namespace SevenCycle.Atlas.Invariants

open Proof Blueprint

def pairWeight (x y : Tuple 3) : ℕ := (∑ k : Fin 3, 4 ^ cycleDistance (x k) (y k)) ^ 2

def energy (C : Finset (Tuple 3)) : ℕ := ∑ x ∈ C, (∑ y ∈ C, pairWeight x y) ^ 2

private theorem distance_preserved : ∀ (b : Bool) (t a c : ZMod 7),
    cycleDistance ((if b then -a else a)+t) ((if b then -c else c)+t) = cycleDistance a c := by
  unfold cycleDistance
  decide

theorem pairWeight_act (g : Isometry 3) (x y : Tuple 3) :
    pairWeight (act g x) (act g y) = pairWeight x y := by
  unfold pairWeight act
  simp_rw [distance_preserved]
  rw [Equiv.sum_comp g.1 (fun j => 4 ^ cycleDistance (x j) (y j))]

theorem energy_act (g : Isometry 3) (C : Finset (Tuple 3)) : energy (actOnCode g C) = energy C := by
  have hi : Set.InjOn (act g) (C : Set (Tuple 3)) := fun _ _ _ _ e => by
    simpa only [Symmetry.undo_act] using congrArg (act (Symmetry.undo g)) e
  simp only [energy, actOnCode, Finset.sum_image hi, pairWeight_act]

/-- Bounded fold over the positions of an array. -/
def sumN (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => sumN f n + f n

theorem sumN_eq (f : ℕ → ℕ) (n : ℕ) : sumN f n = ∑ i : Fin n, f i.val := by
  induction n with
  | zero => simp [sumN]
  | succ n ih => rw [sumN, ih, Fin.sum_univ_castSucc]; rfl

private def fastWeight (x y : Tuple 3) : ℕ :=
  (4 ^ cycleDistance (x 0) (y 0) + 4 ^ cycleDistance (x 1) (y 1) +
   4 ^ cycleDistance (x 2) (y 2)) ^ 2

private theorem fastWeight_eq (x y : Tuple 3) : fastWeight x y = pairWeight x y := by
  simp [fastWeight, pairWeight, Fin.sum_univ_succ, add_assoc]

private def rowEnergy (r : Vector UInt64 7) : ℕ :=
  let a := decodedWords r
  sumN (fun i => (sumN (fun j => fastWeight a[i]! a[j]!) a.size)^2) a.size

private theorem rowEnergy_eq (r : Vector UInt64 7) (hr : rowCheck r = true) :
    rowEnergy r = energy (decodedSet r) := by
  let a := decodedWords r
  have ha := (rowsCheck_sound a (Bool.and_eq_true_iff.mp hr).2).1
  have hi : Set.InjOn (fun i : Fin a.size => a[i]) (Finset.univ : Finset (Fin a.size)) :=
    Finset.injOn_of_card_image_eq (by simpa [rowSet] using ha)
  rw [← decodedWords_set, energy, rowSet]
  change _ = ∑ x ∈ (Finset.univ.image fun i : Fin a.size => a[i]),
    (∑ y ∈ (Finset.univ.image fun i : Fin a.size => a[i]), pairWeight x y)^2
  simp only [Finset.sum_image hi]
  change sumN (fun i => (sumN (fun j => fastWeight a[i]! a[j]!) a.size)^2) a.size = _
  simp only [sumN_eq, getElem!_pos, Fin.isLt, fastWeight_eq]
  rfl

def energiesDistinct (rows : Array (Vector UInt64 7)) : Bool :=
  let energies := rows.map rowEnergy
  let indices := Array.finRange rows.size
  indices.all fun i => indices.all fun j =>
    i == j || energies[i.val]! != energies[j.val]!

/-- A successful uniqueness check separates the orbits of all valid rows. -/
theorem energiesDistinct_sound (rows : Array (Vector UInt64 7)) (ok : energiesDistinct rows = true)
    (valid : rowsValid rows = true) (i j : Fin rows.size) (g : Isometry 3)
    (heq : actOnCode g (decodedSet rows[i]) = decodedSet rows[j]) : i = j := by
  have memRange (k : Fin rows.size) : k ∈ Array.finRange rows.size := Array.mem_ofFn.mpr ⟨k, rfl⟩
  have hr (k : Fin rows.size) : rowCheck rows[k] = true :=
    Array.all_eq_true'.mp valid _ (Array.mem_iff_getElem.mpr ⟨k, k.isLt, rfl⟩)
  have e : rowEnergy rows[i] = rowEnergy rows[j] := by
    rw [rowEnergy_eq _ (hr i), rowEnergy_eq _ (hr j), ← heq, energy_act]
  have hij := Array.all_eq_true'.mp (Array.all_eq_true'.mp ok _ (memRange i)) _ (memRange j)
  by_contra h
  have hne : rowEnergy rows[i.val] ≠ rowEnergy rows[j.val] := by
    simpa [h, getElem!_pos, i.isLt, j.isLt] using hij
  exact hne e

end SevenCycle.Atlas.Invariants

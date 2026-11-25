import SevenCycle.Proof.Bounds
import SevenCycle.Proof.Witness
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Powerset

/-!
# Zero-error codes for the seven-cycle

A coordinate is an element of ℤ/7. Confusability requires all coordinate
differences to lie in the closed radius-one neighbourhood of zero.
-/

namespace SevenCycle

/-- Words of length n over ℤ/7. -/
abbrev Word (n : ℕ) := Fin n → ZMod 7

/-- Distinct words are confusable when every coordinate differs by −1, 0 or 1. -/
def Confusable {n : ℕ} (x y : Word n) : Prop :=
  x ≠ y ∧ ∀ i, x i - y i ∈ ({-1, 0, 1} : Finset (ZMod 7))

/-- A code in the strong power of the seven-cycle. -/
def IsCode {n : ℕ} (C : Finset (Word n)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ¬ Confusable x y

/-- Theorem 1. Every code of length four has at most 112 words. -/
theorem card_le_112 (C : Finset (Word 4)) (hC : IsCode C) : C.card ≤ 112 :=
  Proof.bound_four C hC

/-- Corollary 2. Every code of length five has at most 392 words. -/
theorem card_le_392 (C : Finset (Word 5)) (hC : IsCode C) : C.card ≤ 392 :=
  Proof.five_of_four card_le_112 C hC

instance {n : ℕ} (x y : Word n) : Decidable (Confusable x y) := by
  unfold Confusable
  infer_instance

instance {n : ℕ} (C : Finset (Word n)) : Decidable (IsCode C) := by
  unfold IsCode
  infer_instance

theorem confusable_example : Confusable ![0, 0, 0, 0] ![1, 6, 0, 1] := by decide

/-- The three even residues 0, 2 and 4 are pairwise distinguishable. -/
def example3 : Finset (Word 1) := {![0], ![2], ![4]}

theorem example3_spec : example3.card = 3 ∧ IsCode example3 := by decide

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 20000 in
theorem card_le_three : ∀ C : Finset (Word 1), IsCode C → C.card ≤ 3 := by decide

/-- Projection of the first two layers of the first atlas representative. -/
def example10 : Finset (Word 2) :=
  {![0, 3], ![0, 5], ![2, 3], ![1, 0],
   ![2, 5], ![3, 1], ![4, 4], ![4, 6],
   ![5, 2], ![6, 0]}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem example10_spec : example10.card = 10 ∧ IsCode example10 := by decide

/-- First representative in the released atlas, expanded in coordinate order. -/
def example33 : Finset (Word 3) :=
  {![0, 0, 3], ![0, 0, 5], ![0, 2, 3], ![1, 1, 0],
   ![1, 2, 5], ![1, 3, 1], ![1, 4, 4], ![1, 4, 6],
   ![1, 5, 2], ![1, 6, 0], ![2, 0, 2], ![2, 2, 3],
   ![2, 6, 4], ![3, 0, 0], ![3, 1, 5], ![3, 3, 5],
   ![3, 4, 1], ![3, 4, 3], ![4, 1, 2], ![4, 2, 0],
   ![4, 5, 6], ![4, 6, 2], ![4, 6, 4], ![5, 0, 6],
   ![5, 1, 4], ![5, 3, 2], ![5, 3, 4], ![6, 1, 1],
   ![6, 2, 6], ![6, 4, 0], ![6, 5, 3], ![6, 5, 5],
   ![6, 6, 1]}

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem example33_spec : example33.card = 33 ∧ IsCode example33 := by decide

/-- The four-coordinate witness in the paper’s upper113/example-105.txt. -/
private def rows105 : Array (Word 4) :=
  #[![0, 0, 1, 5], ![0, 0, 3, 1], ![0, 0, 3, 6], ![0, 0, 4, 4],
   ![0, 0, 5, 2], ![0, 0, 6, 5], ![0, 2, 0, 5], ![0, 2, 2, 1],
   ![0, 2, 2, 6], ![0, 2, 5, 5], ![0, 3, 3, 4], ![0, 3, 4, 0],
   ![0, 3, 6, 1], ![0, 4, 1, 1], ![0, 4, 1, 6], ![0, 4, 6, 6],
   ![0, 5, 0, 4], ![0, 5, 3, 0], ![0, 5, 3, 5], ![1, 1, 0, 1],
   ![1, 1, 0, 3], ![1, 1, 2, 3], ![1, 1, 5, 0], ![1, 2, 4, 2],
   ![1, 3, 1, 3], ![1, 3, 6, 3], ![1, 4, 3, 2], ![1, 5, 5, 2],
   ![1, 5, 5, 4], ![1, 6, 0, 0], ![1, 6, 0, 2], ![1, 6, 2, 3],
   ![1, 6, 5, 0], ![2, 0, 4, 2], ![2, 0, 5, 5], ![2, 1, 0, 6],
   ![2, 1, 2, 1], ![2, 1, 2, 6], ![2, 3, 1, 1], ![2, 3, 1, 6],
   ![2, 3, 4, 4], ![2, 3, 6, 1], ![2, 3, 6, 6], ![2, 4, 3, 0],
   ![2, 6, 0, 5], ![2, 6, 2, 1], ![2, 6, 2, 6], ![3, 0, 1, 3],
   ![3, 0, 4, 0], ![3, 0, 6, 1], ![3, 0, 6, 3], ![3, 1, 3, 4],
   ![3, 2, 1, 4], ![3, 2, 4, 1], ![3, 2, 4, 6], ![3, 2, 6, 4],
   ![3, 4, 0, 4], ![3, 4, 2, 4], ![3, 5, 0, 0], ![3, 5, 0, 2],
   ![3, 5, 5, 1], ![3, 5, 5, 3], ![3, 5, 5, 6], ![3, 6, 3, 4],
   ![4, 0, 1, 1], ![4, 0, 1, 6], ![4, 0, 3, 2], ![4, 0, 6, 6],
   ![4, 2, 0, 2], ![4, 2, 1, 0], ![4, 2, 2, 2], ![4, 2, 6, 0],
   ![4, 3, 4, 3], ![4, 4, 2, 2], ![4, 5, 2, 0], ![5, 0, 0, 4],
   ![5, 0, 5, 2], ![5, 0, 5, 4], ![5, 1, 3, 0], ![5, 1, 3, 5],
   ![5, 2, 1, 5], ![5, 2, 6, 5], ![5, 3, 3, 0], ![5, 3, 4, 5],
   ![5, 4, 0, 1], ![5, 4, 0, 6], ![5, 4, 2, 5], ![5, 4, 5, 0],
   ![5, 5, 0, 4], ![5, 6, 3, 5], ![5, 6, 4, 0], ![6, 1, 0, 0],
   ![6, 1, 0, 2], ![6, 1, 2, 3], ![6, 1, 5, 0], ![6, 2, 4, 2],
   ![6, 3, 1, 3], ![6, 3, 6, 3], ![6, 4, 3, 2], ![6, 5, 5, 2],
   ![6, 5, 5, 4], ![6, 6, 0, 2], ![6, 6, 1, 0], ![6, 6, 2, 3],
   ![6, 6, 6, 0]]

def example105 : Finset (Word 4) := Proof.rowSet rows105

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem example105_spec : example105.card = 105 ∧ IsCode example105 :=
  Proof.rowsCheck_sound rows105 (by decide +kernel)

end SevenCycle

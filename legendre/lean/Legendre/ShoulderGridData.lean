import Legendre.AnalyticData
import Legendre.Arithmetic.Cos

namespace Legendre

open Arithmetic
open scoped BigOperators

def shoulderNode (i : ℕ) : ℚ := 1 + (i : ℚ) / 4000

def shoulderNodeUpper (i : ℕ) : ℚ :=
  max 0 (∑ j : Fin 12,
    ((cosPi (((CosineTest.frequency j : ℕ) : ℚ) * shoulderNode i / 4)).smul (twelveWeight j)).hi)

def shoulderLocalHeight (j : ℕ) : ℚ :=
  max (shoulderNodeUpper (j - 1)) (shoulderNodeUpper j) + 2 / (4000 : ℚ) ^ 2

private def shoulderLocalTable : List ℚ :=
  let nodes := Array.ofFn (fun i : Fin 4001 ↦ shoulderNodeUpper i.val)
  List.ofFn (fun i : Fin 4000 ↦
    max (nodes[i.val]'(by simp [nodes]; omega)) (nodes[i.val + 1]'(by simp [nodes]; omega)) +
      2 / (4000 : ℚ) ^ 2)

/-- The suffix maxima, including the final zero height. Index 0 is `e₁`. -/
def shoulderHeightTable : List ℚ := shoulderLocalTable.scanr max 0

/-- The paper's one-based indexing of the certified shoulder heights. -/
def shoulderHeight (j : ℕ) : ℚ := (shoulderHeightTable[j - 1]?).getD 0

private theorem shoulderLocalTable_length : shoulderLocalTable.length = 4000 := by
  simp only [shoulderLocalTable, List.length_ofFn]

private theorem shoulderLocalTable_get (i : ℕ) (hi : i < shoulderLocalTable.length) :
    shoulderLocalTable[i] = shoulderLocalHeight (i + 1) := by
  simp only [shoulderLocalTable, List.getElem_ofFn, Array.getElem_ofFn, shoulderLocalHeight,
    Nat.add_sub_cancel]

theorem shoulderHeight_rec (j : ℕ) (hj : 1 ≤ j) (hj' : j ≤ 4000) :
    shoulderHeight j = max (shoulderLocalHeight j) (shoulderHeight (j + 1)) := by
  have hi : j - 1 < shoulderLocalTable.length := by rw [shoulderLocalTable_length]; omega
  have hs : (j + 1) - 1 < shoulderLocalTable.length + 1 := by rw [shoulderLocalTable_length]; omega
  have heq : j - 1 + 1 = j := by omega
  unfold shoulderHeight shoulderHeightTable
  rw [List.getElem?_scanr_of_lt (by omega : j - 1 < shoulderLocalTable.length + 1),
    List.getElem?_scanr_of_lt hs]
  simp only [Option.getD_some, Nat.add_sub_cancel]
  rw [List.drop_eq_getElem_cons hi, List.foldr_cons, shoulderLocalTable_get, heq]

private theorem foldr_max_nonneg (values : List ℚ) : 0 ≤ values.foldr max 0 := by
  induction values with
  | nil => simp
  | cons x xs ih => exact ih.trans (le_max_right _ _)

theorem shoulderHeight_nonneg (j : ℕ) (hj : j ≤ 4001) : 0 ≤ shoulderHeight j := by
  have hi : j - 1 < shoulderLocalTable.length + 1 := by rw [shoulderLocalTable_length]; omega
  unfold shoulderHeight shoulderHeightTable
  rw [List.getElem?_scanr_of_lt hi, Option.getD_some]
  exact foldr_max_nonneg _

theorem shoulderHeight_last : shoulderHeight 4001 = 0 := by
  have hi : 4001 - 1 < shoulderLocalTable.length + 1 := by rw [shoulderLocalTable_length]; omega
  unfold shoulderHeight shoulderHeightTable
  rw [List.getElem?_scanr_of_lt hi, Option.getD_some, List.drop_eq_nil_of_le]
  · rfl
  · simp [shoulderLocalTable_length]

/-- The numerical test on the first height. All other height properties follow from construction. -/
def checkShoulderHead (data : List ℚ) : Bool :=
  decide (data[0]?.getD 0 < (0.76 : ℚ))

theorem shoulderHeight_first_of_check (h : checkShoulderHead shoulderHeightTable = true) :
    shoulderHeight 1 < 0.76 := by
  simpa [checkShoulderHead, shoulderHeight] using of_decide_eq_true h

end Legendre

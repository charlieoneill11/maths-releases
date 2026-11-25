import Chowla.CheckerMatching
import Mathlib.Algebra.BigOperators.Ring.List

namespace Chowla.Checker

/-- Evaluate a finite list of weighted terms. -/
def weightedSum {α : Type} (terms : List (α × ℚ)) (value : α → ℚ) : ℚ :=
  (terms.map (fun (a, c) => c * value a)).sum

theorem weightedSum_cons {α : Type} (a : α × ℚ) (ts : List (α × ℚ)) (value : α → ℚ) :
    weightedSum (a :: ts) value = a.2 * value a.1 + weightedSum ts value := rfl

theorem weightedSum_append {α : Type} (x y : List (α × ℚ)) (value : α → ℚ) :
    weightedSum (x ++ y) value = weightedSum x value + weightedSum y value := by
  simp [weightedSum]

private def combineWeight {α : Type} [DecidableEq α] (x : α × ℚ) : List (α × ℚ) → List (α × ℚ)
  | [] => [x]
  | y :: ys =>
    if x.1 = y.1 then (x.1, x.2 + y.2) :: ys else x :: y :: ys

/-- Collect adjacent occurrences of the same labelled-choice data. Equal raw data
may combine without an ordering assumption. -/
def collectWeights {α : Type} [DecidableEq α] (xs : List (α × ℚ)) : List (α × ℚ) :=
  xs.foldr combineWeight []

private theorem weightedSum_combine {α : Type} [DecidableEq α] (x : α × ℚ)
    (ys : List (α × ℚ)) (value : α → ℚ) :
    weightedSum (combineWeight x ys) value = x.2 * value x.1 + weightedSum ys value := by
  cases ys with
  | nil => rfl
  | cons y ys =>
    change weightedSum
      (if x.1 = y.1 then (x.1, x.2 + y.2) :: ys else x :: y :: ys) value = _
    by_cases h : x.1 = y.1
    · rw [if_pos h]
      simp only [weightedSum_cons, h]
      ring
    · rw [if_neg h, weightedSum_cons]

theorem collectWeights_sound {α : Type} [DecidableEq α] (xs : List (α × ℚ)) (value : α → ℚ) :
    weightedSum (collectWeights xs) value = weightedSum xs value := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    change weightedSum (combineWeight a (collectWeights as)) value = _
    rw [weightedSum_combine, ih, weightedSum_cons]

theorem weightedSum_perm {α : Type} {xs ys : List (α × ℚ)} (h : xs.Perm ys) (value : α → ℚ) :
    weightedSum xs value = weightedSum ys value := by
  exact (h.map (fun p : α × ℚ => p.2 * value p.1)).sum_eq

/-- A repeated width leaves the same list after deleting any adjacent occurrence. Thus
the grouped deletion list keeps the exact labelled multiplicity of that choice. -/
def groupedChoices (widths : List ℚ) : List ((ℚ × List ℚ) × ℚ) :=
  collectWeights ((eraseEach widths).map (fun choice => (choice, 1)))

theorem groupedChoices_sound (widths : List ℚ) (value : ℚ × List ℚ → ℚ) :
    weightedSum (groupedChoices widths) value = ((eraseEach widths).map value).sum := by
  rw [groupedChoices, collectWeights_sound]
  simp [weightedSum, Function.comp_def]

end Chowla.Checker

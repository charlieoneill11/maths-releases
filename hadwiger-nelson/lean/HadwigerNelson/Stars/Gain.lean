import HadwigerNelson.Stars.OneBadEdge
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! The deterministic gain form of the one-bad-edge inequality. -/

open scoped BigOperators

namespace HadwigerNelson.Stars

variable {V : Type*}

/-- The excess at a vertex, expressed in the scalar field of the probability integral. -/
noncomputable def gain (E : Finset (V × V)) (κ : V → Option (Fin 6)) (v : V) : ℝ :=
  (sameCount E κ v : ℝ) - locked E κ v

theorem gain_nonneg (E : Finset (V × V)) (κ : V → Option (Fin 6)) (v : V) :
    0 ≤ gain E κ v := by
  exact sub_nonneg.mpr (by exact_mod_cast locked_le_sameCount E κ v)

/-- Equation (3), before averaging over placements. -/
theorem one_bad_edge_gain (S : Finset V) (E : Finset (V × V)) (κ : V → Option (Fin 6)) (Y : ℕ)
    (ends : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S) (loops : ∀ e ∈ E, e.1 ≠ e.2)
    (component : (∃ v ∈ S, κ v = none) → 1 ≤ Y)
    (impossible : ¬ ∃ c : V → Fin 6, ∀ e ∈ E, c e.1 ≠ c e.2) :
    1 ≤ (Y : ℝ) + badCount E κ - (∑ v ∈ S, gain E κ v) / 4 := by
  classical
  have h : (4 : ℝ) ≤ 4 * Y + 2 * badCount E κ + ∑ v ∈ S, (locked E κ v : ℝ) := by
    exact_mod_cast one_bad_edge S E κ Y ends loops component impossible
  have c : ∑ v ∈ S, (sameCount E κ v : ℝ) = 2 * badCount E κ := by
    exact_mod_cast sum_sameCount S E κ ends
  simp only [gain, Finset.sum_sub_distrib, c]
  linarith

end HadwigerNelson.Stars

import HadwigerNelson.Proof.UnionEdges
import HadwigerNelson.Stars.CellScore
import HadwigerNelson.Stars.PlacementAverage

namespace HadwigerNelson.Proof
open MeasureTheory

/-- A uniform lower bound on the physical per-incidence score supplies the
star credit for every finite edge list, including isolated vertices. -/
theorem gain_of_cell_score_for_palette (W : Wave.Datum) (palette : Wave.Label ≃ Fin 6) (β : ℝ)
    (bound : ∀ {d : Nat}, 0<d → ∀ φ : Fin d → ℝ, β ≤ Stars.cellScore W φ)
    (E : Finset (Plane × Plane)) (unit : ∀ e ∈ E, dist e.1 e.2 = 1) (v : Plane) :
    β * Stars.degree E v ≤ ∫ ω, Stars.gain E (fun x => (Placement.colour W ω x).map palette) v ∂Placement.law W := by
  rcases Nat.eq_zero_or_pos (Stars.degree E v) with zero | pos
  · rw [zero,Nat.cast_zero,mul_zero]
    exact integral_nonneg fun ω => Stars.gain_nonneg E _ v
  · obtain ⟨φ,eq⟩ := Stars.integral_gain_eq_cell W palette E unit v
    have score := bound pos φ
    have hr : (0:ℝ) < Stars.degree E v := by exact_mod_cast pos
    rw [eq]
    exact (le_div_iff₀ hr).mp score

/-- The same estimate for the canonical enumeration of wave labels. -/
theorem gain_of_cell_score (W : Wave.Datum) (β : ℝ)
    (bound : ∀ {d : Nat}, 0<d → ∀ φ : Fin d → ℝ, β ≤ Stars.cellScore W φ)
    (E : Finset (Plane × Plane)) (unit : ∀ e ∈ E, dist e.1 e.2 = 1) (v : Plane) :
    β * Stars.degree E v ≤ ∫ ω, Stars.gain E (placedColours W ω) v ∂Placement.law W :=
  gain_of_cell_score_for_palette W palette β bound E unit v

end HadwigerNelson.Proof

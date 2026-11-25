import HadwigerNelson.Placement.Edge
import HadwigerNelson.Placement.UnitDirection
import HadwigerNelson.Placement.Derandomisation

namespace HadwigerNelson.Proof
open MeasureTheory
noncomputable section

/-- Translate the two tile families and three row residues into the public palette. -/
def palette : Wave.Label ≃ Fin 6 :=
  Fintype.equivOfCardEq (by simp [Wave.Label, ZMod.card])

def placedColours (W : Wave.Datum) (ω : Placement.Sample) (v : Plane) : Option (Fin 6) :=
  (Placement.colour W ω v).map palette

/-- First milestone from a complete wave with a certified one-edge probability. -/
theorem edges_of_union_bound (W : Wave.Datum) (p : ℝ) (E : Finset (Plane × Plane))
    (unit : ∀ e ∈ E, dist e.1 e.2 = 1)
    (full : ∀ v, ∀ᵐ ω ∂Placement.law W, (Placement.colour W ω v).isSome = true)
    (bound : Placement.meanMonoProb W ≤ p) (small : (E.card : ℝ) * p < 1) :
    ∃ c : Plane → Fin 6, ∀ e ∈ E, c e.1 ≠ c e.2 := by
  classical
  have hf : ∀ᵐ ω ∂Placement.law W, ∀ e ∈ E,
      (Placement.colour W ω e.1).isSome = true ∧ (Placement.colour W ω e.2).isSome = true :=
    (Filter.eventually_all_finset E).mpr fun e _ => (full e.1).and (full e.2)
  obtain ⟨c, hc⟩ := Placement.colourable_of_edge_prob (μ := Placement.law W) E
    (Placement.colour W) (false, 0) p hf
    (fun e _ => Placement.integrable_sameColour W (Placement.continuous_place e.1).measurable
      (Placement.continuous_place e.2).measurable)
    (fun e he => by
      obtain ⟨φ, hφ⟩ := Placement.rotated_unit_displacement (unit e he)
      exact (Placement.edge_probability_of_direction W e.1 e.2 φ hφ).le.trans bound) small
  exact ⟨fun v => palette (c v), fun e he => fun h => hc e he (palette.injective h)⟩

end
end HadwigerNelson.Proof

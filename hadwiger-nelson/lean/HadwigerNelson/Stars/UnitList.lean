import HadwigerNelson.Stars.Directions
import HadwigerNelson.Placement.UnitDirection

namespace HadwigerNelson.Stars
noncomputable section

/-- List the relative unit directions at a vertex, once per incidence.
The same phases work for all translations and all rotation angles. -/
theorem exists_incidence_angles (E : Finset (Plane × Plane))
    (unit : ∀ e ∈ E, dist e.1 e.2 = 1) (v : Plane) :
    ∃ φ : Fin (degree E v) → ℝ, ∀ j, ∀ θ,
      Placement.rotate θ (otherEnd (incidenceEquiv E v j).val) - Placement.rotate θ v =
      direction (θ+φ j) := by
  classical
  have distance (x : ↥(incidences E v)) : dist v (otherEnd x.val) = 1 := by
    obtain ⟨x,hx⟩ := x
    rcases x with e | e
    · simp [incidences] at hx
      simpa [otherEnd,hx.2] using unit e hx.1
    · simp [incidences] at hx
      simpa [otherEnd,hx.2,dist_comm] using unit e hx.1
  choose φ hφ using fun j => Placement.rotated_unit_displacement (distance (incidenceEquiv E v j))
  exact ⟨φ,hφ⟩

/-- Replacing the finite graph by the list of colours at the displaced unit
directions preserves its exact gain for every placement. -/
theorem placed_gain_eq_score (E : Finset (Plane × Plane)) (v : Plane) (W : Wave.Datum)
    (p : Wave.Label ≃ Fin 6) (φ : Fin (degree E v) → ℝ)
    (hφ : ∀ j, ∀ θ, Placement.rotate θ (otherEnd (incidenceEquiv E v j).val) -
      Placement.rotate θ v = direction (θ+φ j)) (ω : Placement.Sample) :
    gain E (fun x => (Placement.colour W ω x).map p) v =
      angleScore W φ (Placement.place ω v) ω.1 := by
  have shift (j) : Placement.place ω (otherEnd (incidenceEquiv E v j).val) =
      Placement.place ω v + direction (ω.1+φ j) := by
    rw [← hφ j ω.1]
    unfold Placement.place
    abel
  rw [gain_eq_local]
  unfold Placement.colour angleScore
  simp_rw [shift]
  exact localGain_relabel p _ _

end
end HadwigerNelson.Stars

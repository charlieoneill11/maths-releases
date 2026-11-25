import HadwigerNelson.Proof.UnionEdges
import HadwigerNelson.Stars.Integrability
import HadwigerNelson.Proof.EdgeArithmetic

namespace HadwigerNelson.Proof
open MeasureTheory
noncomputable section

theorem badIndicator_eq (W : Wave.Datum) (e : Plane × Plane) (ω : Placement.Sample) :
    Stars.badIndicator (placedColours W ω) e =
      Placement.sameColour W (Placement.place ω e.1) (Placement.place ω e.2) := by
  classical
  unfold Stars.badIndicator Stars.Bad placedColours Placement.colour Placement.sameColour
  cases Wave.colour W (Placement.place ω e.1) <;>
    cases Wave.colour W (Placement.place ω e.2) <;> simp

theorem measurable_placedColour (W : Wave.Datum) (v : Plane) (k : Option (Fin 6)) :
    MeasurableSet {ω | placedColours W ω v = k} := by
  cases k with
  | none =>
    simpa [placedColours, Placement.colour] using
      (Wave.blank_closed W).measurableSet.preimage (Placement.continuous_place v).measurable
  | some k =>
    have h : {ω | placedColours W ω v = some k} =
        (fun ω => Placement.place ω v) ⁻¹' {z | Wave.colour W z = some (palette.symm k)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, placedColours, Placement.colour]
      cases Wave.colour W (Placement.place ω v) <;> simp [Equiv.eq_symm_apply]
    rw [h]
    exact (Wave.colour_fibre_open W _).measurableSet.preimage
      (Placement.continuous_place v).measurable

theorem unit_edge_mean (W : Wave.Datum) (e : Plane × Plane) (he : dist e.1 e.2 = 1) :
    (∫ ω, Stars.badIndicator (placedColours W ω) e ∂Placement.law W) = Placement.meanMonoProb W := by
  obtain ⟨φ, hφ⟩ := Placement.rotated_unit_displacement he
  simp only [badIndicator_eq]
  exact Placement.edge_probability_of_direction W e.1 e.2 φ hφ

/-- Section 4 using the measured gain per incidence at the actual placed colours. -/
theorem edges_of_star_bound (W : Wave.Datum) (p β : ℝ) (E : Finset (Plane × Plane))
    (unit : ∀ e ∈ E, dist e.1 e.2 = 1)
    (full : ∀ v, ∀ᵐ ω ∂Placement.law W, (Placement.colour W ω v).isSome = true)
    (bound : Placement.meanMonoProb W ≤ p)
    (stars : ∀ v, β * Stars.degree E v ≤
      ∫ ω, Stars.gain E (placedColours W ω) v ∂Placement.law W)
    (small : (E.card : ℝ) * (p - β / 2) < 1) :
    ∃ c : Plane → Fin 6, ∀ e ∈ E, c e.1 ≠ c e.2 := by
  classical
  let S := E.image Prod.fst ∪ E.image Prod.snd
  have ends (e) (he : e ∈ E) : e.1 ∈ S ∧ e.2 ∈ S :=
    ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ he),
     Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)⟩
  apply Stars.colourable_of_locked_gain (μ := Placement.law W) S E (placedColours W) p β ends _ _ _ _ _ _ small
  · intro e he h
    have := unit e he
    simp [h] at this
  · apply (Filter.eventually_all_finset S).mpr
    intro v _
    simpa [placedColours] using full v
  · intro e _
    simp_rw [badIndicator_eq]
    exact Placement.integrable_sameColour W (Placement.continuous_place e.1).measurable
      (Placement.continuous_place e.2).measurable
  · exact fun e he => (unit_edge_mean W e (unit e he)).le.trans bound
  · intro v hv
    exact Stars.integrable_gain S E v hv ends _ (fun x _ => measurable_placedColour W x)
  · exact fun v _ => stars v

end
end HadwigerNelson.Proof

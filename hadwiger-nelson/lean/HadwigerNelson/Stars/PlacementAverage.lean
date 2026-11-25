import HadwigerNelson.Stars.UnitList
import HadwigerNelson.Stars.AngularGainMeasure
import HadwigerNelson.Placement.CellMeasure
import HadwigerNelson.Placement.Edge

namespace HadwigerNelson.Stars
open MeasureTheory Set
noncomputable section

/-- First average the angle at a fixed physical centre and then integrate
the centre over one period cell, normalized by its Euclidean area. -/
theorem integral_gain_eq_cell (W : Wave.Datum) (p : Wave.Label ≃ Fin 6)
    (E : Finset (Plane × Plane)) (unit : ∀ e ∈ E, dist e.1 e.2 = 1) (v : Plane) :
    ∃ φ : Fin (degree E v) → ℝ,
      (∫ ω, gain E (fun x => (Placement.colour W ω x).map p) v ∂Placement.law W) =
      (6*W.x*Wave.H)⁻¹ * ∫ z in Wave.cell W (3*Wave.H), angularGain W φ z := by
  obtain ⟨φ,hφ⟩ := exists_incidence_angles E unit v
  refine ⟨φ,?_⟩
  simp_rw [placed_gain_eq_score E v W p φ hφ]
  let angle := Placement.uniformInterval (2*Real.pi)
  let tr := Placement.translationLaw W
  have whole : Integrable (fun ω : Placement.Sample => angleScore W φ (Placement.place ω v) ω.1)
      (angle.prod tr) := integrable_angleScore W φ measurable_fst (Placement.continuous_place v).measurable
  have spatial (θ : ℝ) :
      (∫ t, angleScore W φ (Placement.place (θ,t) v) θ ∂tr) =
        ∫ t, angleScore W φ (Placement.translationPoint t) θ ∂tr := by
    apply Placement.translation_average_invariant W (fun z => angleScore W φ z θ) (Placement.rotate θ v)
    · exact angleScore_lattice W φ θ
    · exact integrable_angleScore W φ measurable_const Placement.continuous_translationPoint.measurable
    · exact integrable_angleScore W φ measurable_const
        (measurable_const.add Placement.continuous_translationPoint.measurable)
  have full : Integrable (fun q : Placement.Sample => angleScore W φ (Placement.translationPoint q.2) q.1)
      (angle.prod tr) := integrable_angleScore W φ measurable_fst
      (Placement.continuous_translationPoint.measurable.comp measurable_snd)
  change (∫ ω, _ ∂angle.prod tr) = _
  rw [integral_prod _ whole]
  simp_rw [spatial]
  rw [integral_integral_swap (f := fun θ t => angleScore W φ (Placement.translationPoint t) θ) full]
  change (∫ t, angularGain W φ (Placement.translationPoint t) ∂Placement.translationLaw W) = _
  rw [← integral_map Placement.continuous_translationPoint.measurable.aemeasurable
    (measurable_angularGain W φ).aestronglyMeasurable,Placement.translationLaw_map,integral_smul_measure]
  have pos : 0 ≤ 6*W.x*Wave.H := by have := W.x_bounds.1; have := Wave.H_pos; positivity
  simp [ENNReal.toReal_ofReal pos]

end
end HadwigerNelson.Stars

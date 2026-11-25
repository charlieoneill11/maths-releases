import HadwigerNelson.Placement.Measure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! A null blank set remains null for every vertex of a finite placed edge family. -/

open MeasureTheory Set Filter

namespace HadwigerNelson.Placement

noncomputable section

theorem uniformInterval_ac (T : ℝ) : uniformInterval T ≪ volume :=
  Measure.smul_absolutelyContinuous.trans Measure.restrict_le_self.absolutelyContinuous

theorem translationLaw_ac (W : Wave.Datum) : translationLaw W ≪ volume :=
  (uniformInterval_ac _).prod (uniformInterval_ac _)

theorem translationPoint_preserves_volume : MeasurePreserving translationPoint volume volume := by
  exact (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm

/-- A Lebesgue-null blank set in the Euclidean plane is avoided by the random translation
for each fixed rotation, even before taking the average over angles. -/
theorem placed_nonblank_ae (W : Wave.Datum) (x : Plane)
    (hnull : volume {z | Wave.colour W z = none} = 0) :
    ∀ᵐ ω ∂law W, (colour W ω x).isSome = true := by
  have hm : MeasurableSet {ω | (colour W ω x).isSome = true} := by
    have he : {ω | (colour W ω x).isSome = true} =
        ((fun ω ↦ place ω x) ⁻¹' {z | Wave.colour W z = none})ᶜ := by
      ext ω
      cases h : Wave.colour W (place ω x) <;> simp [colour, h]
    rw [he]
    exact ((Wave.blank_closed W).measurableSet.preimage (continuous_place x).measurable).compl
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  refine .of_forall fun θ ↦ ?_
  have preserve := (measurePreserving_add_left (volume : Measure Plane) (rotate θ x)).comp
    translationPoint_preserves_volume
  have hzero := (translationLaw_ac W) (preserve.quasiMeasurePreserving.preimage_null hnull)
  rw [ae_iff]
  convert hzero using 2
  ext t
  change (¬ (Wave.colour W (rotate θ x + translationPoint t)).isSome = true) ↔
    Wave.colour W (rotate θ x + translationPoint t) = none
  cases Wave.colour W (rotate θ x + translationPoint t) <;> simp

theorem endpoints_nonblank_ae (W : Wave.Datum) (edges : Finset (Plane × Plane))
    (hnull : volume {z | Wave.colour W z = none} = 0) :
    ∀ᵐ ω ∂law W, ∀ e ∈ edges,
      (colour W ω e.1).isSome = true ∧ (colour W ω e.2).isSome = true := by
  apply eventually_finset_ball.mpr
  intro e _
  exact (placed_nonblank_ae W e.1 hnull).and (placed_nonblank_ae W e.2 hnull)

end
end HadwigerNelson.Placement

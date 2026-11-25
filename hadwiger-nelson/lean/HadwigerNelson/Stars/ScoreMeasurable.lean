import HadwigerNelson.Stars.Directions
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

namespace HadwigerNelson.Stars
open MeasureTheory Set
noncomputable section

variable {α : Type*} [MeasurableSpace α] {d : Nat}

theorem measurable_angleScore (W : Wave.Datum) (φ : Fin d → ℝ)
    {θ : α → ℝ} {z : α → Plane} (hθ : Measurable θ) (hz : Measurable z) :
    Measurable (fun a => angleScore W φ (z a) (θ a)) := by
  letI : MeasurableSpace (Option Wave.Label) := ⊤
  have hc : Measurable (Wave.colour W) := by
    apply measurable_to_countable'
    intro b
    cases b with
    | none => exact (Wave.blank_closed W).measurableSet
    | some c => exact (Wave.colour_fibre_open W c).measurableSet
  have hd : Continuous direction := Placement.continuous_point Real.continuous_cos Real.continuous_sin
  let n (a : α) (j : Fin d) := Wave.colour W (z a + direction (θ a+φ j))
  have hn : Measurable n := measurable_pi_lambda _ fun j =>
    hc.comp (hz.add (hd.measurable.comp (hθ.add measurable_const)))
  let f (t : Option Wave.Label × (Fin d → Option Wave.Label)) := localGain t.1 t.2
  let pair (a : α) := (Wave.colour W (z a), n a)
  have mf : Measurable f := measurable_of_countable f
  have mp : Measurable pair := (hc.comp hz).prodMk hn
  change Measurable (f ∘ pair)
  exact mf.comp mp

end
end HadwigerNelson.Stars

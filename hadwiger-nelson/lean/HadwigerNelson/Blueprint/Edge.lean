import HadwigerNelson.Blueprint.Milestone
import HadwigerNelson.Proof.PlacedEdges
import HadwigerNelson.Native.Stars.Complete
import HadwigerNelson.Native.Stars.Layout

namespace HadwigerNelson
open MeasureTheory
noncomputable section

/-- Proposition 25 for the complete wave, with degrees counting the actual input incidences. -/
theorem Stars.complete_locked (E : Finset (Plane × Plane))
    (unit : ∀ e ∈ E, dist e.1 e.2 = 1) (v : Plane) :
    (8 / 10^9 : ℝ) * Stars.degree E v ≤
      ∫ ω, Stars.gain E (Proof.placedColours Wave.completeDatum ω) v ∂Placement.law Wave.completeDatum :=
  Stars.BoxCheck.complete_gain_of_check Stars.BoxCheck.sourceBoxes_checked Stars.BoxCheck.complete_checked E unit v

/-- The unconditional edge bound with the per-incidence locked-star improvement. -/
theorem complete_edge_bound (E : Finset (Plane × Plane)) (hE : ∀ e ∈ E, dist e.1 e.2 = 1)
    (hcard : E.card ≤ 245510) : ∃ c : Plane → Fin 6, ∀ e ∈ E, c e.1 ≠ c e.2 := by
  apply Proof.edges_of_star_bound Wave.completeDatum (Angular.completeUpper : ℝ) (8 / 10^9) E
    hE Wave.complete_ae_nonblank Wave.complete_monoProb_upper (Stars.complete_locked E hE)
  apply Proof.mul_lt_one_of_card_le hcard
  have h : (245510 : ℝ) * ((Angular.completeUpper : ℝ) - 4/10^9) < 1 := by
    norm_num [Angular.completeUpper]
  linarith

end
end HadwigerNelson

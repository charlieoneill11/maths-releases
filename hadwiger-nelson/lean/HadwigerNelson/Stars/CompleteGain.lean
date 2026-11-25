import HadwigerNelson.Stars.BoxFamilies
import HadwigerNelson.Stars.CompleteCheck
import HadwigerNelson.Proof.StarGain

namespace HadwigerNelson.Stars.BoxCheck

/-- Assemble the real per-box estimates and the two finite certificates
to give the expected gain of an arbitrary placed vertex. -/
theorem complete_gain_of_boxes (layout : checkSourceBoxes = true) (tests : checkComplete = true)
    (harmonic : ∀ {d : Nat}, 0<d → d≤27 → ∀ (k : Fin harmonics) (ψ : Fin d → ℝ)
      (i : Fin 14464) z, z ∈ physicalSource (source i.val) →
      (d:ℝ)/2 * harmonicLocal k ψ i ≤ angularGain Wave.completeDatum ψ z)
    (native : ∀ {d : Nat}, 23<d → ∀ (ψ : Fin d → ℝ) (i : Fin 252) z,
      z ∈ physicalSource (saturated i.val) →
      (d:ℝ) * saturatedLocal d i ≤ angularGain Wave.completeDatum ψ z)
    (E : Finset (Plane × Plane)) (unit : ∀ e ∈ E, dist e.1 e.2=1) (v : Plane) :
    (8/10^9 : ℝ) * degree E v ≤
      ∫ ω, gain E (Proof.placedColours Wave.completeDatum ω) v ∂Placement.law Wave.completeDatum := by
  apply Proof.gain_of_cell_score Wave.completeDatum _ _ E unit v
  intro d hd φ
  exact cellScore_eight layout tests hd φ (harmonic hd) native

end HadwigerNelson.Stars.BoxCheck

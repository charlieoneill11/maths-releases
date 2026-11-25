import HadwigerNelson.Stars.CopyArea
import HadwigerNelson.Stars.AngularGainMeasure

namespace HadwigerNelson.Stars
open MeasureTheory Set
noncomputable section

def cellScore {d : Nat} (W : Wave.Datum) (φ : Fin d → ℝ) : ℝ :=
  ((6*W.x*Wave.H)⁻¹ * ∫ z in Wave.cell W (3*Wave.H), angularGain W φ z) / d

/-- Apply the local estimates to all twelve images. A reflection reverses
the neighbour angles, so the estimate is required for each reflected list.
A common rotation has already been removed by the full-turn angle average. -/
theorem normalized_cell_box_sum {d : Nat} {ι : Type*} (W : Wave.Datum)
    (hd : 0<d) (φ : Fin d → ℝ) (S : Finset ι) (B : ι → Set Plane)
    (u : (Fin d → ℝ) → ι → ℝ)
    (meas : ∀ i ∈ S, MeasurableSet (B i))
    (inside : ∀ i ∈ S, B i ⊆ Wave.halfTile W false)
    (apart : ∀ i ∈ S, ∀ j ∈ S, ∀ z, z ∈ B i → z ∈ B j → i=j)
    (invariant : ∀ i ∈ S, ∀ b h, u (fun j => signAngle b h (φ j)) i = u φ i)
    (lower : ∀ ψ i, i ∈ S → ∀ z ∈ B i, (d:ℝ)/2*u ψ i ≤ angularGain W ψ z) :
    (∑ i ∈ S, volume.real (B i)/(W.x*Wave.H)*u φ i) ≤ cellScore W φ := by
  letI : IsFiniteMeasure (volume.restrict (Wave.cell W (3*Wave.H))) :=
    isFiniteMeasure_restrict.mpr (by rw [Wave.lattice_covolume]; exact ENNReal.ofReal_ne_top)
  have physical := twelve_copy_sum W S B (fun i => (d:ℝ)/2*u φ i) (angularGain W φ) meas inside apart
    (fun g z => by simpa only [add_comm (g:Plane)] using angularGain_period W φ z g g.property)
    (measurable_angularGain W φ) (integrable_angularGain W φ _)
    (Filter.Eventually.of_forall fun z => (angularGain_range W φ z).1)
    (fun ⟨b,h,k⟩ i hi => Filter.Eventually.of_forall fun _ ⟨z,hz,eq⟩ => by
      rw [← eq,copyIso_apply,angularGain_copy]
      simpa only [invariant i hi b h] using lower (fun j => signAngle b h (φ j)) i hi z hz)
  have hx : 0 < W.x := by linarith [W.x_bounds.1]
  have hr : (0:ℝ)<d := by exact_mod_cast hd
  have hh := Wave.H_pos
  unfold cellScore
  rw [le_div_iff₀ hr,← div_eq_inv_mul,le_div_iff₀ (show 0<6*W.x*Wave.H by positivity)]
  calc
    _ = 12 * (∑ i ∈ S, volume.real (B i)*((d:ℝ)/2*u φ i)) := by
      rw [Finset.sum_mul,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp
      ring
    _ ≤ _ := physical

end
end HadwigerNelson.Stars

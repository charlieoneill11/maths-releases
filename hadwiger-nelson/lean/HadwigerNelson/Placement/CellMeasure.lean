import HadwigerNelson.Placement.Blank
import HadwigerNelson.Wave.Geometry.Fundamental
import Mathlib.MeasureTheory.Measure.WithDensity

namespace HadwigerNelson.Placement
open MeasureTheory Set
open scoped ENNReal
noncomputable section

/-- Uniform translation in the two rectangle coordinates, expressed as
normalised Lebesgue area in the Euclidean plane. -/
theorem translationLaw_map (W : Wave.Datum) :
    Measure.map translationPoint (translationLaw W) =
      (ENNReal.ofReal (6*W.x*Wave.H))⁻¹ • volume.restrict (Wave.cell W (3*Wave.H)) := by
  have unif (T : ℝ) : uniformInterval T =
      (ENNReal.ofReal T)⁻¹ • volume.restrict (Ico 0 T) := by
    rw [uniformInterval, Measure.restrict_congr_set Ico_ae_eq_Ioc]
  have rect : translationPoint ⁻¹' Wave.cell W (3*Wave.H) =
      (Ico 0 (2*W.x)) ×ˢ (Ico 0 (3*Wave.H)) := rfl
  have hx : 0 ≤ 2*W.x := by linarith [W.x_bounds.1]
  have hh : 0 ≤ 3*Wave.H := by linarith [Wave.H_pos]
  have mass : (ENNReal.ofReal (2*W.x))⁻¹ * (ENNReal.ofReal (3*Wave.H))⁻¹ =
      (ENNReal.ofReal (6*W.x*Wave.H))⁻¹ := by
    rw [show 6*W.x*Wave.H=(2*W.x)*(3*Wave.H) by ring, ENNReal.ofReal_mul hx,
      ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inl ENNReal.ofReal_ne_top)]
  rw [translationLaw, unif, unif, Measure.prod_smul_left, Measure.prod_smul_right,
    smul_smul, mass, Measure.prod_restrict, Measure.map_smul, ← rect]
  congr 1
  change Measure.map translationPoint (volume.restrict (translationPoint ⁻¹' _)) = _
  rw [← Measure.restrict_map continuous_translationPoint.measurable (Wave.cell_measurable W _),
    translationPoint_preserves_volume.map_eq]

end
end HadwigerNelson.Placement

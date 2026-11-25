import HadwigerNelson.Angular.Scaled
import HadwigerNelson.Angular.PhysicalBox
import HadwigerNelson.Angular.Checker

namespace HadwigerNelson.Angular
open MeasureTheory

/-- Twice the real area cut out of the fixed piecewise-linear profile, measured
in square units of the integer profile grid. The upper endpoint equals the
lower one whenever the vertical displacement reaches the tile height. -/
noncomputable def sliceMass (d lo : Int) : ℝ :=
  2*(CompleteWave.scale:ℝ)^2 *
    (∫ y in (lo:ℝ)/CompleteWave.scale..(max (CompleteWave.height:Int) lo : Int)/(CompleteWave.scale:ℝ),
      max 0 (CompleteWave.rightAt y-(d:ℝ)/CompleteWave.scale))

/-- A successful numeric shard bounds the real weighted integral enclosures
of both same-colour displacements for every bin in its angle range. -/
theorem checkGroup_integral_bound {k upper : Nat} (hk : k < 32)
    (ok : checkGroup k upper = true) :
    (∑ i ∈ Finset.range (2^23),
      let j := k*2^23+i
      let b := halfAngleBox (2^28) j (j+1)
      (sliceMass b.xlo b.ylo + sliceMass b.shiftX b.shiftY) *
        (2^28:ℝ)/((2^28:ℝ)^2+(j:ℝ)^2)) ≤ upper := by
  apply le_trans _ (checkGroup_sound hk ok)
  apply Finset.sum_le_sum
  intro i _
  dsimp only
  let b := halfAngleBox (2^28) (k*2^23+i) (k*2^23+i+1)
  have h₁ := slice_scaled_le b.xlo b.ylo (ylo_nonneg ..)
  have h₂ := slice_scaled_le b.shiftX b.shiftY (shiftY_nonneg _)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  simpa only [boxArea,Int.cast_add,sliceMass] using add_le_add h₁ h₂

end HadwigerNelson.Angular

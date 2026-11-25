import HadwigerNelson.Stars.Directions
import HadwigerNelson.Placement.Law
import HadwigerNelson.Placement.Period

namespace HadwigerNelson.Stars
open MeasureTheory
noncomputable section

def angularGain {d : Nat} (W : Wave.Datum) (φ : Fin d → ℝ) (z : Plane) : ℝ :=
  ∫ θ, angleScore W φ z θ ∂Placement.uniformInterval (2*Real.pi)

theorem angularGain_period {d : Nat} (W : Wave.Datum) (φ : Fin d → ℝ) (z v : Plane)
    (hv : v ∈ Wave.lattice W) : angularGain W φ (z+v) = angularGain W φ z := by
  unfold angularGain angleScore
  simp only [add_right_comm z v, Wave.colour_periodic W _ v hv]

/-- A reflected box tests the reflected list of relative angles. Averaging
over a full turn removes the common offset and the reflection of the angle. -/
theorem angularGain_copy {d : Nat} (W : Wave.Datum) (φ : Fin d → ℝ)
    (z : Plane) (b h : Bool) (k : Fin 3) :
    angularGain W φ (copyMap b h k z) = angularGain W (fun j => signAngle b h (φ j)) z := by
  let F := angleScore W (fun j => signAngle b h (φ j)) z
  have per : Function.Periodic F (2*Real.pi) := angleScore_period W (fun j => signAngle b h (φ j)) z
  rw [angularGain,angularGain,Placement.integral_uniformInterval (by positivity),
    Placement.integral_uniformInterval (by positivity)]
  congr 1
  simp_rw [angleScore_copy W φ z b h k]
  change (∫ θ in 0..2*Real.pi, F (turnAngle b h θ)) = ∫ θ in 0..2*Real.pi, F θ
  by_cases eq : b=h
  · simpa only [turnAngle,signAngle,if_pos eq,add_comm (if b then Real.pi else 0)] using
      Placement.integral_translate_period per (if b then Real.pi else 0)
  · simpa only [turnAngle,signAngle,if_neg eq,← sub_eq_add_neg] using
      Placement.integral_reverse_period per (if b then Real.pi else 0)

end
end HadwigerNelson.Stars

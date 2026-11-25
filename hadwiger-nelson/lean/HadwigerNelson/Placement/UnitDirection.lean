import HadwigerNelson.Placement.Coordinates
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace HadwigerNelson.Placement

/-- Rotating a fixed unit displacement adds the rotation angle to its phase.
The pair may start anywhere in the plane. -/
theorem rotated_unit_displacement {x y : Plane} (hxy : dist x y = 1) :
    ∃ φ : ℝ, ∀ θ, rotate θ y - rotate θ x =
      Wave.point (Real.cos (θ+φ)) (Real.sin (θ+φ)) := by
  let z : ℂ := ⟨y 0 - x 0, y 1 - x 1⟩
  have hcoord : (y 0-x 0)^2 + (y 1-x 1)^2 = 1 := by
    have h := EuclideanSpace.dist_sq_eq y x
    rw [dist_comm y x, hxy, Fin.sum_univ_two] at h
    simpa [Real.dist_eq, sq_abs] using h.symm
  have hnorm : ‖z‖ = 1 := by
    rw [Complex.norm_def]
    have hn : Complex.normSq z = 1 := by
      simpa [z, Complex.normSq_apply, pow_two] using hcoord
    rw [hn, Real.sqrt_one]
  have hc : Real.cos z.arg = y 0 - x 0 := by
    simpa [hnorm, z] using Complex.norm_mul_cos_arg z
  have hs : Real.sin z.arg = y 1 - x 1 := by
    simpa [hnorm, z] using Complex.norm_mul_sin_arg z
  refine ⟨z.arg, fun θ => ?_⟩
  ext i
  fin_cases i <;> simp [rotate, Real.cos_add, Real.sin_add, hc, hs] <;> ring

end HadwigerNelson.Placement

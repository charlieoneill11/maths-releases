import HadwigerNelson.Placement.Coordinates
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace HadwigerNelson.Placement
noncomputable section

theorem coord_dist_sq (x y : Plane) :
    dist x y ^ 2 = (x 0-y 0)^2+(x 1-y 1)^2 := by
  simpa [Fin.sum_univ_two, Real.dist_eq, sq_abs] using EuclideanSpace.dist_sq_eq x y

theorem rotate_sub (θ : ℝ) (x y : Plane) : rotate θ (x-y) = rotate θ x - rotate θ y := by
  ext i
  fin_cases i <;> simp [rotate] <;> ring

theorem rotate_dist (θ : ℝ) (x y : Plane) : dist (rotate θ x) (rotate θ y) = dist x y := by
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [coord_dist_sq, coord_dist_sq]
  simp only [rotate,Wave.point_fst,Wave.point_snd]
  linear_combination ((x 0-y 0)^2+(x 1-y 1)^2) * Real.sin_sq_add_cos_sq θ

theorem rotate_coord_difference_le (θ : ℝ) (x y : Plane) (i : Fin 2) :
    |rotate θ x i - rotate θ y i| ≤ dist x y := by
  rw [← rotate_dist θ x y,dist_eq_norm]
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (rotate θ x - rotate θ y) i

end
end HadwigerNelson.Placement

import HadwigerNelson.Blueprint.Point.Crossings
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

namespace HadwigerNelson.Centres

private theorem coordSq (p q : Plane) :
    dist p q^2 = (p 0-q 0)^2+(p 1-q 1)^2 := by
  simpa [Fin.sum_univ_two,Real.dist_eq,sq_abs] using EuclideanSpace.dist_sq_eq p q

/-- Affine and metric conclusions of Lemma 46 for four distinct unit incidences. -/
theorem rhombus_geometry (p q u v : Plane) (hpq : p ≠ q) (huv : u ≠ v)
    (hup : dist u p = 1) (huq : dist u q = 1) (hvp : dist v p = 1) (hvq : dist v q = 1) :
    p + q = u + v ∧ dist u v = Real.sqrt (4 - dist p q ^ 2) ∧
      inner ℝ (u - v) (q - p) = 0 := by
  have unit {x y : Plane} (h : dist x y = 1) :
      (x 0-y 0)^2+(x 1-y 1)^2 = 1 := by rw [← coordSq,h]; norm_num
  let a := q 0 - p 0
  let b := q 1 - p 1
  let c := u 0 - v 0
  let d := u 1 - v 1
  let x := p 0 + q 0 - u 0 - v 0
  let y := p 1 + q 1 - u 1 - v 1
  -- Subtract the four squared incidence equations to isolate the diagonal directions.
  have orth : a*c+b*d=0 := by
    dsimp [a,b,c,d]
    linear_combination (unit hup - unit huq - unit hvp + unit hvq)/2
  have perp1 : x*a+y*b=0 := by
    dsimp [x,y,a,b]
    linear_combination (unit huq - unit hup + unit hvq - unit hvp)/2
  have perp2 : x*c+y*d=0 := by
    dsimp [x,y,c,d]
    linear_combination (unit hvp - unit hup + unit hvq - unit huq)/2
  -- The diagonals are nonzero and orthogonal, so they span the plane.
  have det : a*d-b*c ≠ 0 := by
    intro hz
    have positive : 0 < c^2+d^2 := (coordSq u v) ▸ sq_pos_of_pos (dist_pos.mpr huv)
    have ha : a*(c^2+d^2)=0 := by linear_combination c*orth+d*hz
    have hb : b*(c^2+d^2)=0 := by linear_combination d*orth-c*hz
    have a0 := (mul_eq_zero.mp ha).resolve_right positive.ne'
    have b0 := (mul_eq_zero.mp hb).resolve_right positive.ne'
    have h1 : 0 < a^2+b^2 := (coordSq q p) ▸ sq_pos_of_pos (dist_pos.mpr hpq.symm)
    simp [a0,b0] at h1
  have hx : x=0 := by
    have z : x*(a*d-b*c)=0 := by linear_combination d*perp1-b*perp2
    exact (mul_eq_zero.mp z).resolve_right det
  have hy : y=0 := by
    have z : y*(a*d-b*c)=0 := by linear_combination a*perp2-c*perp1
    exact (mul_eq_zero.mp z).resolve_right det
  have eqdiag : dist u v ^ 2 + dist p q ^ 2 = 4 := by
    have z : x^2+y^2=0 := by simp [hx,hy]
    dsimp [x,y] at z
    rw [coordSq u v,coordSq p q]
    linear_combination unit hup + unit huq + unit hvp + unit hvq - z
  refine ⟨?_,?_,?_⟩
  · ext i
    fin_cases i
    · change p 0+q 0=u 0+v 0
      dsimp [x] at hx
      linarith
    · change p 1+q 1=u 1+v 1
      dsimp [y] at hy
      linarith
  · rw [show 4-dist p q^2=dist u v^2 by linarith, Real.sqrt_sq dist_nonneg]
  · simpa [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, a,b,c,d, mul_comm] using orth

end HadwigerNelson.Centres

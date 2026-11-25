import HadwigerNelson.Packing.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace HadwigerNelson.Packing

/-- The maximum of a monic quadratic on an interval is bounded by its two endpoint values. -/
private theorem quad_bound {l x u b c M : ℝ} (hl : l ≤ x) (hu : x ≤ u)
    (lo : l^2+b*l+c ≤ M) (hi : u^2+b*u+c ≤ M) : x^2+b*x+c ≤ M := by
  by_cases h : 0 ≤ u+x+b
  · nlinarith only [hi, mul_nonneg (sub_nonneg.mpr hu) h]
  · nlinarith only [lo, mul_nonneg (sub_nonneg.mpr hl) (show 0 ≤ -(l+x+b) by linarith)]

/-- A common bound on the four corner values bounds all squared radial distances in the
annulus. The cross term can also be used for the rational close-pair estimates. -/
theorem radial_corners {l u x y C M : ℝ} (hx : x ∈ Set.Icc l u) (hy : y ∈ Set.Icc l u)
    (ll : l^2+l^2-2*l*l*C ≤ M) (lu : l^2+u^2-2*l*u*C ≤ M)
    (uu : u^2+u^2-2*u*u*C ≤ M) : x^2+y^2-2*x*y*C ≤ M := by
  have endY (a : ℝ) (lo : a^2+l^2-2*a*l*C ≤ M) (hi : a^2+u^2-2*a*u*C ≤ M) :
      a^2+y^2-2*a*y*C ≤ M := by
    have h := quad_bound (b := -2*a*C) (c := a^2) hy.1 hy.2
      (by linarith [lo] : l^2+(-2*a*C)*l+a^2 ≤ M) (by linarith [hi] : u^2+(-2*a*C)*u+a^2 ≤ M)
    linarith
  have left := endY l ll lu
  have right := endY u (by linarith [lu]) uu
  have h := quad_bound (b := -2*y*C) (c := y^2) hx.1 hx.2
    (by linarith [left] : l^2+(-2*y*C)*l+y^2 ≤ M)
    (by linarith [right] : u^2+(-2*y*C)*u+y^2 ≤ M)
  linarith

theorem corner_unit {l u x y : ℝ} (hl : 0 < l) (hu : 0 < u)
    (hx : x ∈ Set.Icc l u) (hy : y ∈ Set.Icc l u) :
    x^2+y^2-2*x*y*annulusCosine l u ≤ 1 := by
  let C := annulusCosine l u
  have lo : (2*l^2-1)/(2*l^2) ≤ C := le_max_left _ _
  have mid : (l^2+u^2-1)/(2*l*u) ≤ C := (le_max_left ..).trans (le_max_right ..)
  have hi : (2*u^2-1)/(2*u^2) ≤ C := (le_max_right ..).trans (le_max_right ..)
  have lq := (div_le_iff₀ (show 0 < 2*l^2 by positivity)).mp lo
  have mq := (div_le_iff₀ (show 0 < 2*l*u by positivity)).mp mid
  have uq := (div_le_iff₀ (show 0 < 2*u^2 by positivity)).mp hi
  apply radial_corners hx hy <;> change _ - _*C ≤ _ <;> linarith

end HadwigerNelson.Packing

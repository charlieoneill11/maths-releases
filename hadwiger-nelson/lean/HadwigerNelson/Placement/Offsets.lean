import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.Linarith

/-! Support restrictions select only two lattice offsets in the first quadrant (Lemma 10). -/

namespace HadwigerNelson.Placement

/-- A tile overlap has width strictly below one and height one half. Only two periods of the
staggered lattice can contribute for a displacement in the first unit quadrant. -/
theorem quadrant_lattice_offsets {x u v : ℝ} (i j : ℤ) (hx : 9/10 < x)
    (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1) (hv₀ : 0 ≤ v) (hv₁ : v ≤ 1)
    (hu : |u - 2*x*i| < 1) (hv : |v - (3/4*i + 3/2*j)| < 1/2) :
    (i = 0 ∨ i = 1) ∧ j = 0 := by
  obtain ⟨hul, hur⟩ := abs_lt.mp hu
  obtain ⟨hvl, hvr⟩ := abs_lt.mp hv
  have hx₀ : 0 ≤ x := by linarith
  have hi₀ : 0 ≤ i := by
    by_contra h
    have h' : (i : ℝ) ≤ -1 := by exact_mod_cast (show i ≤ -1 by omega)
    nlinarith [mul_nonneg hx₀ (show 0 ≤ -(i : ℝ) - 1 by linarith)]
  have hi₁ : i ≤ 1 := by
    by_contra h
    have h' : (2 : ℝ) ≤ i := by exact_mod_cast (show 2 ≤ i by omega)
    nlinarith [mul_nonneg hx₀ (show 0 ≤ (i : ℝ) - 2 by linarith)]
  have hi : i = 0 ∨ i = 1 := by omega
  refine ⟨hi, ?_⟩
  by_contra h
  have hj : j ≤ -1 ∨ 1 ≤ j := by omega
  rcases hj with hj | hj
  · have hj' : (j : ℝ) ≤ -1 := by exact_mod_cast hj
    have hi' : (i : ℝ) ≤ 1 := by exact_mod_cast hi₁
    linarith
  · have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hi' : (0 : ℝ) ≤ i := by exact_mod_cast hi₀
    linarith

end HadwigerNelson.Placement

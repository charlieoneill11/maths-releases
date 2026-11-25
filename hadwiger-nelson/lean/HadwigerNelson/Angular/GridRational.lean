import HadwigerNelson.Angular.Grid
import HadwigerNelson.Wave.Geometry

namespace HadwigerNelson.Angular.Grid

private def piece (v : Nat → ℚ) (n i : Nat) : ℚ × ℚ × ℚ × ℚ :=
  ((i:ℚ)/(2*n),((i:ℚ)+1)/(2*n),(v (i+1)-v i)*(2*n),v i-(v (i+1)-v i)*i)

/-- A uniform finite table of rational ordinates has a rational affine
presentation on the closed height interval in Definition 4. -/
theorem rationalProfile (v : Nat → ℚ) (n : Nat) (hn : 0<n) :
    Wave.RationalProfile (fun y => interpolation (fun i => (v i : ℝ)) n ((2*n:ℝ)*y)) := by
  classical
  refine ⟨(Finset.range n).image (piece v n),?_⟩
  intro y hy
  have npos : (0:ℝ) < n := by exact_mod_cast hn
  have pos : (0:ℝ)<2*n := by positivity
  have ny : (2*n:ℝ)*y ∈ Set.Icc 0 (n:ℝ) := by
    constructor
    · exact mul_nonneg pos.le hy.1
    · have h := hy.2
      unfold Wave.H at h
      nlinarith [mul_nonneg (show 0 ≤ (1:ℝ)/2-y by linarith) npos.le]
  obtain ⟨i,hi,lo,up⟩ := hasCell hn ny
  refine ⟨piece v n i, Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩,?_,?_⟩
  · change (((i:ℚ)/(2*n):ℚ):ℝ) ≤ y ∧ y ≤ ((((i:ℚ)+1)/(2*n):ℚ):ℝ)
    push_cast
    constructor
    · apply (div_le_iff₀ pos).2
      linarith only [lo, mul_comm y (2*(n:ℝ))]
    · apply (le_div_iff₀ pos).2
      linarith only [up, mul_comm y (2*(n:ℝ))]
  · intro z _ hz
    change (((i:ℚ)/(2*n):ℚ):ℝ) ≤ z ∧ z ≤ ((((i:ℚ)+1)/(2*n):ℚ):ℝ) at hz
    push_cast at hz
    have cell : (2*n:ℝ)*z ∈ Set.Icc (i:ℝ) ((i:ℝ)+1) := by
      rcases hz with ⟨l,h⟩
      rw [div_le_iff₀ pos] at l
      rw [le_div_iff₀ pos] at h
      simpa [mul_comm z (2*(n:ℝ))] using And.intro l h
    dsimp only
    rw [interpolation_on _ hi cell]
    dsimp [piece]
    push_cast
    ring

end HadwigerNelson.Angular.Grid

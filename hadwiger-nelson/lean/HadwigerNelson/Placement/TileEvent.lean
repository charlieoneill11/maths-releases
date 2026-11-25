import HadwigerNelson.Wave.Geometry
import HadwigerNelson.Placement.Offsets

/-! Reduction of the first-quadrant event on the source tile to two possible destination tiles. -/

namespace HadwigerNelson.Placement

open Wave

private theorem point_ext' {x y : Plane} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  ext i
  fin_cases i <;> assumption

/-- The source tile occupies strictly less than unit width and has height `H`. -/
theorem tile_coord_bounds (W : Datum) {z : Plane} (hz : z ∈ tile W) :
    (0 < z 0 ∧ z 0 < 1) ∧ (0 < z 1 ∧ z 1 < H) :=
  ⟨⟨lt_of_le_of_lt (W.left_bounds _).1 hz.2.1, hz.2.2.trans (W.right_bounds _).2⟩, hz.1⟩

theorem colour_on_tile (W : Datum) (z : Plane) (hz : z ∈ Wave.tile W) :
    Wave.colour W z = some (false,0) := by
  apply (Wave.colourClass_iff W z _).mpr
  refine ⟨0,0,rfl,(Wave.inCopy_iff_tile W false 0 0 _).mpr ?_⟩
  have he : point (z 0) (z 1) = z := by ext i; fin_cases i <;> rfl
  simpa [localU, localY, he] using hz

/-- Exactly one copy of the first colour can meet the fundamental rectangle. The strict
profile and tile boundaries allow the closed rectangle to be used in the forward implication. -/
theorem first_colour_in_rectangle (W : Datum) (z : Plane)
    (hu : z 0 ∈ Set.Icc 0 (2*W.x)) (hy : z 1 ∈ Set.Icc 0 (3*H))
    (hc : Wave.colour W z = some (false,0)) : z ∈ tile W := by
  obtain ⟨i,k,hk,ht⟩ := (Wave.colourClass_iff W z _).mp hc
  obtain ⟨j,rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd k 3).mp hk
  have hd := (inCopy_iff_tile W false i (3*j) z).mp ht
  obtain ⟨⟨ha,hb⟩,⟨hv,hw⟩⟩ := tile_coord_bounds W hd
  simp only [point_fst, point_snd, localU, localY, Bool.false_eq_true, if_false,
    add_zero, Int.cast_mul, Int.cast_ofNat] at ha hb hv hw
  have hxn : 0 ≤ W.x := by linarith [W.x_bounds.1]
  have hi : i = 0 := by
    by_contra hh
    rcases (show i ≤ -1 ∨ 1 ≤ i by omega) with hi | hi
    · have hi' : (i : ℝ) ≤ -1 := by exact_mod_cast hi
      nlinarith [mul_nonneg hxn (show 0 ≤ -(i : ℝ) - 1 by linarith),hu.1,W.x_bounds.1]
    · have hi' : (1 : ℝ) ≤ i := by exact_mod_cast hi
      nlinarith [mul_nonneg hxn (show 0 ≤ (i : ℝ)-1 by linarith),hu.2]
  subst i
  simp [H] at hv hw hy
  have hj : j = 0 := by
    by_contra hh
    rcases (show j ≤ -1 ∨ 1 ≤ j by omega) with hj | hj
    · have hj' : (j : ℝ) ≤ -1 := by exact_mod_cast hj
      linarith [hy.1]
    · have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
      linarith [hy.2]
  subst j
  have ep : point (z 0) (z 1) = z := point_ext' rfl rfl
  simpa [localU,localY,ep] using hd

/-- Among the points of the source tile, a nonblank match in the first quadrant comes from
the source tile or its nearest staggered neighbour. Both offsets refer to the original lattice. -/
theorem tile_matching_offsets (W : Datum) (z : Plane) (u v : ℝ)
    (hz : z ∈ tile W) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (hmatch : Wave.colour W (z + point u v) = some (false, 0)) :
    z + point u v ∈ tile W ∨ z + point u v - latticePoint W 1 0 ∈ tile W := by
  obtain ⟨i,k,hk,hc⟩ := (Wave.colourClass_iff W _ _).mp hmatch
  obtain ⟨j,rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd k 3).mp hk
  have hd := (inCopy_iff_tile W false i (3*j) _).mp hc
  have he : point (localU W false i (z + point u v))
      (localY false i (z + point u v) - ((3*j : ℤ) : ℝ)*H) =
        z + point u v - latticePoint W i j := by
    apply point_ext' <;> simp [latticePoint,localU,localY] <;> ring
  rw [he] at hd
  have ⟨⟨hx₀,hx₁⟩,⟨hy₀,hy₁⟩⟩ := tile_coord_bounds W hz
  have ⟨⟨ha₀,ha₁⟩,⟨hb₀,hb₁⟩⟩ := tile_coord_bounds W hd
  simp [latticePoint,H] at ha₀ ha₁ hb₀ hb₁
  have hun : |u-2*W.x*i| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hvn : |v-(3/4*i+3/2*j)| < 1/2 := by
    unfold H at hy₁
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  obtain ⟨hi,rfl⟩ := quadrant_lattice_offsets i j W.x_bounds.1 hu.1 hu.2 hv.1 hv.2 hun hvn
  rcases hi with rfl | rfl
  · left
    have zero : latticePoint W 0 0 = 0 := by apply point_ext' <;> simp [latticePoint]
    simpa [zero] using hd
  · exact Or.inr hd

end HadwigerNelson.Placement

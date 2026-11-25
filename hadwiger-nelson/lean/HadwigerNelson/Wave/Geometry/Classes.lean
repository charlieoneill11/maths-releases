import HadwigerNelson.Wave.Geometry

namespace HadwigerNelson.Wave
noncomputable section

/-- Embed a point of the basic tile in the first or reflected tile at column i and row j. -/
def putInCopy (W : Datum) (b : Bool) (i j : ℤ) (q : Plane) : Plane :=
  point (if b then 2*W.x*((i:ℝ)+1)-q 0 else 2*W.x*i+q 0)
    ((3/2)*H*i+j*H+q 1-(if b then H/2 else 0))

private theorem coords_putInCopy (W : Datum) (b : Bool) (i j : ℤ) (q : Plane) :
    point (localU W b i (putInCopy W b i j q))
      (localY b i (putInCopy W b i j q)-j*H) = q := by
  ext h
  fin_cases h <;> cases b <;> simp [localU,localY,putInCopy] <;> ring

private theorem putInCopy_coords (W : Datum) (b : Bool) (i j : ℤ) (z : Plane) :
    putInCopy W b i j (point (localU W b i z) (localY b i z-j*H)) = z := by
  ext h
  fin_cases h <;> cases b <;> simp [localU,localY,putInCopy] <;> ring

theorem inCopy_iff_image (W : Datum) (b : Bool) (i j : ℤ) (z : Plane) :
    InCopy W b i j z ↔ z ∈ putInCopy W b i j '' tile W := by
  rw [inCopy_iff_tile]
  constructor
  · intro hz
    exact ⟨_,hz,putInCopy_coords ..⟩
  · rintro ⟨q,hq,rfl⟩
    rwa [coords_putInCopy]

theorem putInCopy_translate (W : Datum) (b : Bool) (i j k : ℤ) (q : Plane) :
    putInCopy W b i (j+3*k) q = putInCopy W b 0 j q + latticePoint W i k := by
  ext h
  fin_cases h <;> cases b <;> simp [putInCopy,latticePoint] <;> ring

/-- The colour class is exactly the period-translates of a single tile. Its
orientation is encoded by b. Different copies of this tile are disjoint
by InCopy.unique. -/
theorem colourClass_translates (W : Datum) (b : Bool) (j : ℤ) (z : Plane) :
    colour W z = some (b,(j:ZMod 3)) ↔
      ∃ v ∈ lattice W, ∃ q ∈ tile W, z = putInCopy W b 0 j q + v := by
  rw [colourClass_iff]
  constructor
  · rintro ⟨i,r,hr,h⟩
    have modEq := (ZMod.intCast_eq_intCast_iff' r j 3).mp hr
    let k := (r-j)/3
    have row : r = j+3*k := by dsimp [k]; omega
    obtain ⟨q,hq,rfl⟩ := (inCopy_iff_image ..).mp h
    exact ⟨latticePoint W i k,(mem_lattice ..).2 ⟨i,k,rfl⟩,q,hq,
      by rw [row,putInCopy_translate]⟩
  · rintro ⟨v,hv,q,hq,rfl⟩
    obtain ⟨i,k,rfl⟩ := (mem_lattice ..).mp hv
    refine ⟨i,j+3*k,?_,?_⟩
    · push_cast
      simp [show (3:ZMod 3)=0 by decide]
    · rw [← putInCopy_translate,inCopy_iff_image]
      exact ⟨q,hq,rfl⟩

end
end HadwigerNelson.Wave

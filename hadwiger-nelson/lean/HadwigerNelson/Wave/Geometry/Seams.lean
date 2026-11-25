import HadwigerNelson.Wave.Geometry.Blank
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

namespace HadwigerNelson.Wave
noncomputable section

def graphLine (a b : ℝ) : AffineSubspace ℝ Plane where
  carrier := {z | z 0 = a*z 1 + b}
  smul_vsub_vadd_mem := by
    intro c p q r hp hq hr
    change c*(p 0 - q 0)+r 0 = a*(c*(p 1-q 1)+r 1)+b
    change p 0 = _ at hp
    change q 0 = _ at hq
    change r 0 = _ at hr
    rw [hp,hq,hr]
    ring

def horizontalLine (b : ℝ) : AffineSubspace ℝ Plane where
  carrier := {z | z 1 = b}
  smul_vsub_vadd_mem := by
    intro c p q r hp hq hr
    change c*(p 1-q 1)+r 1 = b
    change p 1 = _ at hp
    change q 1 = _ at hq
    change r 1 = _ at hr
    rw [hp,hq,hr]
    ring

def verticalSupports (W : Datum) : Set Plane :=
  ⋃ i : ℤ, (graphLine 0 (2*W.x*i) : Set Plane)

def horizontalSupports : Set Plane :=
  ⋃ i : ℤ, ⋃ j : ℤ, (horizontalLine ((3/2)*H*i+j*H/2) : Set Plane)

def seamSupports (W : Datum) : Set Plane :=
  ⋃ i : ℤ, ⋃ j : ℤ, ⋃ a : ℚ, ⋃ b : ℚ,
    (graphLine a (2*W.x*i-(a:ℝ)*((3/2)*H*i+j*H)+b) : Set Plane)

/-- All exceptional boundaries lie on a countable collection of affine lines.
The two profile coefficients are rational on each of finitely many pieces. -/
theorem seams_subset_supports (W : Datum) : seams W ⊆ verticalSupports W ∪ (horizontalSupports ∪ seamSupports W) := by
  rintro z (⟨i,hu⟩ | ⟨i,j,hy⟩ | ⟨i,hg⟩)
  · left
    refine Set.mem_iUnion.mpr ⟨i,?_⟩
    change z 0=0*z 1+2*W.x*i
    simpa using hu
  · right; left
    refine Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨j,?_⟩⟩
    change z 1 = (3/2)*H*i+j*H/2
    linarith
  · right; right
    let t := z 1-(3/2)*H*i
    let j := ⌊t/H⌋
    let w := t-j*H
    have hlo := (le_div_iff₀ H_pos).mp (Int.floor_le (t/H))
    have hhi := (div_lt_iff₀ H_pos).mp (Int.lt_floor_add_one (t/H))
    have hw : w ∈ Set.Icc 0 H := by dsimp [w,j]; constructor <;> linarith
    obtain ⟨pieces,hp⟩ := W.right_rational
    obtain ⟨p,_,hi,form⟩ := hp w hw
    obtain ⟨_,_,a,b⟩ := p
    have formula := form w hw hi
    have hper : W.right w = W.right t := W.right_periodic.sub_int_mul_eq j
    refine Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨a,Set.mem_iUnion.mpr ⟨b,?_⟩⟩⟩⟩
    change z 0=(a:ℝ)*z 1 + (2*W.x*i-(a:ℝ)*((3/2)*H*i+j*H)+b)
    change W.right w = (a:ℝ)*w+b at formula
    rw [hper] at formula
    dsimp [w,t] at formula
    linarith

end
end HadwigerNelson.Wave

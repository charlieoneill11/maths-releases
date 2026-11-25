import HadwigerNelson.Stars.StripGeometry
import HadwigerNelson.Wave.Geometry
import Mathlib.Tactic.IntervalCases

/-! Identification of the release's integer labels with the actual complete-wave
colour classes. On the reflected side, the geometric column is m−1 and the
geometric row is j+2. -/

namespace HadwigerNelson.Stars.BoxCheck
open CompleteWave (height scale xInt)

def reflected (c : Nat) : Bool := !(c ≤ 3)
def colLift (c : Nat) (m : Int) := if c ≤ 3 then m else m-1
def rowLift (c : Nat) (j : Int) := if c ≤ 3 then j else j+2
def rowResidue (c : Nat) : Int := if c ≤ 3 then 1-(c : Int) else 6-(c : Int)

def actualLabel (c : Nat) : Wave.Label := (reflected c, (rowResidue c : ZMod 3))

theorem code_iff_residue (c : Nat) (hc : 1 ≤ c ∧ c ≤ 6) (j : Int) :
    code c j = c ↔ (rowLift c j : ZMod 3) = (actualLabel c).2 := by
  change _ ↔ ((rowLift c j : Int) : ZMod 3) = ((rowResidue c : Int) : ZMod 3)
  rw [ZMod.intCast_eq_intCast_iff']
  obtain ⟨h0,h1⟩ := hc
  interval_cases c <;> norm_num [code,rowLift,rowResidue] <;> omega

noncomputable def scaledWall (W : Wave.Datum) (y : ℝ) : ℝ :=
  (scale : ℝ)*W.right (y/scale)

private theorem timeShift (m : Int) : (3*m*(height : Int)/2 : Int) = 750000000000*m := by
  norm_num [height,scale]
  omega

/-- Unscale a local row, using periodicity to evaluate the right wall at
the local height shifted back to the master band. -/
private theorem unscale (W : Wave.Datum) (j : Int) (u v : ℝ) :
    InStrip (scaledWall W) j (scale*u) (scale*v) ↔
    (j : ℝ)*Wave.H < v ∧ v < ((j : ℝ)+1)*Wave.H ∧ 0 < u ∧ u < W.right v := by
  have shift : ((scale : ℝ)*v-j*height)/scale = v-j*Wave.H := by
    norm_num [scale,height,Wave.H]
    ring
  simp only [InStrip,scaledWall,shift,W.right_periodic.sub_int_mul_eq]
  norm_num [scale,height,Wave.H]
  constructor
  all_goals rintro ⟨a,b,c,d⟩
  all_goals refine ⟨?_,?_,?_,?_⟩ <;> linarith

/-- Each scaled strip coincides with its physical tile copy, with all seams open. -/
theorem strip_iff_copy (W : Wave.Datum)
    (hX : W.x = (xInt : ℝ)/scale) (hL : ∀ y, W.left y = 0)
    (c : Nat) (m j : Int) (z : Plane) :
    InStrip (scaledWall W) j (columnX c m (scale*z 0)) (columnY m (scale*z 1)) ↔
    Wave.InCopy W (reflected c) (colLift c m) (rowLift c j) z := by
  let u := if c ≤ 3 then z 0-2*W.x*m else 2*W.x*m-z 0
  let v := z 1-3/2*Wave.H*m
  have xeq : columnX c m (scale*z 0) = scale*u := by
    by_cases hc : c ≤ 3 <;> simp [columnX,u,hX,hc] <;> norm_num [scale,xInt] <;> ring
  have yeq : columnY m (scale*z 1) = scale*v := by
    simp [columnY,timeShift,v,scale,Wave.H]
    ring
  rw [xeq,yeq,unscale]
  by_cases hc : c ≤ 3
  · simp [Wave.InCopy,Wave.localY,Wave.localU,reflected,colLift,rowLift,hc,hL,u,v]
  · have ys : Wave.localY true (m-1) z = v+2*Wave.H := by
      simp [Wave.localY,v]
      ring
    have us : Wave.localU W true (m-1) z = u := by
      simp [Wave.localU,u,hc]
    have per : W.right (v+2*Wave.H) = W.right v := by
      simpa using (W.right_periodic.int_mul 2) v
    simp only [Wave.InCopy,reflected,colLift,rowLift,hc,decide_false,Bool.not_false,if_false,
      ys,us,hL,per,Int.cast_add,Int.cast_ofNat]
    constructor
    all_goals rintro ⟨a,b,c,d⟩
    all_goals exact ⟨by linarith,by linarith,c,d⟩

theorem hasCode_iff_colour (W : Wave.Datum)
    (hX : W.x = (xInt : ℝ)/scale) (hL : ∀ y, W.left y = 0)
    (c : Nat) (hc : 1 ≤ c ∧ c ≤ 6) (z : Plane) :
    HasCode (scaledWall W) c (scale*z 0) (scale*z 1) ↔ Wave.colour W z = some (actualLabel c) := by
  rw [Wave.colourClass_iff]
  constructor
  · rintro ⟨m,j,hj,h⟩
    exact ⟨colLift c m,rowLift c j,(code_iff_residue c hc j).1 hj,
      (strip_iff_copy W hX hL c m j z).1 h⟩
  · rintro ⟨i,l,hl,hh⟩
    let m := if c ≤ 3 then i else i+1
    let j := if c ≤ 3 then l else l-2
    have hi : colLift c m = i := by by_cases hc : c ≤ 3 <;> simp [m,colLift,hc]
    have hj : rowLift c j = l := by by_cases hc : c ≤ 3 <;> simp [j,rowLift,hc]
    refine ⟨m,j,(code_iff_residue c hc j).2 (by simpa [hj] using hl),
      (strip_iff_copy W hX hL c m j z).2 ?_⟩
    simpa only [hi,hj,actualLabel] using hh

end HadwigerNelson.Stars.BoxCheck

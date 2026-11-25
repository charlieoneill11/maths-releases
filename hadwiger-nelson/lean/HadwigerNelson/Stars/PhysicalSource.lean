import HadwigerNelson.Stars.SourceBoxes
import HadwigerNelson.Stars.PhysicalEnvelope
import HadwigerNelson.Placement.TileEvent
import HadwigerNelson.Wave.Geometry.Halves

namespace HadwigerNelson.Stars.BoxCheck
open CompleteWave (scale xInt)

def physicalSource (s : Source) : Set Plane :=
  {z | InSource s (10^6*z 0) (10^6*z 1)}

theorem source_in_box {s : Source} {z : Plane} (hz : z ∈ physicalSource s) :
    InBox s.box (scale*z 0) (scale*z 1) := by
  obtain ⟨a,b,c,d⟩ := hz
  simp only [InBox, Source.box,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,scale,Nat.cast_pow,Nat.cast_ofNat]
  constructor
  · linarith
  refine ⟨by linarith,by linarith,by linarith⟩

private theorem actual_half_tile (s : Source) (hx : 0 ≤ s.xlo ∧ s.xhi ≤ 1000000)
    (hy : 0 ≤ s.ylo ∧ s.yhi ≤ 250000) (status : classify s.box 1 = .inside) :
    physicalSource s ⊆ Wave.halfTile Wave.completeDatum false := by
  intro z hz
  have ux : (0 : ℝ) ≤ s.xlo ∧ (s.xhi : ℝ) ≤ 1000000 := by exact_mod_cast hx
  have vy : (0 : ℝ) ≤ s.ylo ∧ (s.yhi : ℝ) ≤ 250000 := by exact_mod_cast hy
  have ⟨a,b,c,d⟩ := hz
  have zx : 0 ≤ z 0 ∧ z 0 ≤ 1 := ⟨by linarith [ux.1],by linarith [ux.2]⟩
  have zy : 0 ≤ z 1 ∧ z 1 < Wave.H / 2 := by
    unfold Wave.H; constructor <;> linarith [vy.1,vy.2]
  have window : -(2*(scale : ℝ)) ≤ scale*z 0 ∧ scale*z 0 ≤ 2*(scale:ℝ) := by
    norm_num [scale]; constructor <;> linarith [zx.1,zx.2]
  have code := (classify_sound completeWallBounds _ 1 _ _ (source_in_box hz) window gap_complete).1 status
  have color := (hasCode_iff_colour _ Wave.completeDatum_x Wave.completeDatum_left 1 (by decide) z).1 code
  refine ⟨Placement.first_colour_in_rectangle Wave.completeDatum z ⟨zx.1,?_⟩ ⟨zy.1,?_⟩ color,zy.2⟩
  · linarith [Wave.completeDatum.x_bounds.1,zx.2]
  · linarith [Wave.H_pos,zy.2]

theorem physical_source_half (i : Fin 14464) (h : sourceValid i.val = true) :
    physicalSource (source i.val) ⊆ Wave.halfTile Wave.completeDatum false := by
  have ⟨_,_,yl,yh,xl,xh,_,_,st,_⟩ := sourceValid_spec h
  have zones (k : Nat) (hk : k < 4) : 0 ≤ zoneLeft k ∧ zoneRight k ≤ 1000000 := by
    interval_cases k <;> decide
  have limits := zones _ (first_zone i)
  exact actual_half_tile _ ⟨limits.1.trans xl,xh.trans limits.2⟩ ⟨yl,yh⟩ st

theorem physical_saturated_half (i : Fin 252) (h : saturatedValid i.val = true) :
    physicalSource (saturated i.val) ⊆ Wave.halfTile Wave.completeDatum false := by
  obtain ⟨a,b,c,d⟩ := saturated_limits i
  exact actual_half_tile _ ⟨a,by omega⟩ ⟨c,by omega⟩ (beq_iff_eq.mp h)

end HadwigerNelson.Stars.BoxCheck

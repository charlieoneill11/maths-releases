import HadwigerNelson.Certificate.Hole.Slabs
import HadwigerNelson.Certificate.Hole.Grid
import HadwigerNelson.Certificate.Hole.Tables
import HadwigerNelson.Wave.Holes.Lower

namespace HadwigerNelson.Certificate.Hole
open Wave
noncomputable section

/-- Evaluate the fixed-grid lower enclosure at real displacement bounds. The
vertical and horizontal displacements are each rounded up to a picounit. -/
def physical (x y : ℝ) : ℝ :=
  (ticks ⌈x*10^12⌉ ⌈y*10^12⌉ : ℝ)/(denom:ℝ)

private theorem down_width (W : Datum) (p : Centres.partialProfile W) (z : ℤ) (hz : |z|≤cutoff) :
    tickDown (W.left ((z:ℝ)/10^12)) = (width z:ℝ)/10^12 := by
  unfold tickDown
  rw [width_floor W p z hz]

private theorem height_eq (W : Datum) (p : Centres.partialProfile W) (dx dy z : ℤ)
    (hz : |z| ≤ cutoff) (hz' : |z-dy| ≤ cutoff) :
    let a := tickDown (W.left ((z:ℝ)/10^12))
    let b := tickDown (W.left ((z:ℝ)/10^12-(dy:ℝ)/10^12))
    min (2*a) (min (2*b) (a+b-(dx:ℝ)/10^12)) = (height dx dy z:ℝ)/10^12 := by
  dsimp only
  rw [← sub_div,← Int.cast_sub,down_width W p z hz,down_width W p (z-dy) hz']
  simp only [height,Int.cast_min,Int.cast_mul,Int.cast_ofNat,Int.cast_add,Int.cast_sub,
    ← mul_div_assoc,← add_div,← sub_div,min_div_div_right (by norm_num : (0:ℝ)≤10^12)]

theorem physical_eq_holeLower (W : Datum) (p : Centres.partialProfile W) (x y : ℝ) (hy : 0≤y) :
    physical x y = holeLower W x y (gridY ⌈y*10^12⌉) := by
  let dx := ⌈x*10^12⌉
  let dy := ⌈y*10^12⌉
  have hn : 0≤dy := Int.ceil_nonneg (by positivity)
  have hi : 2*W.y0 ≤ tickUp y ↔ 2*cutoff ≤ dy := by
    rw [p.2.1]
    unfold tickUp
    change (2*(918/100000) : ℝ) ≤ (dy:ℝ)/10^12 ↔ _
    rw [le_div_iff₀ (by norm_num)]
    norm_num [cutoff,step]
    exact_mod_cast Iff.rfl
  unfold physical holeLower
  dsimp only
  by_cases outside : 2*cutoff ≤ dy
  · rw [if_pos (hi.mpr outside)]
    change (ticks dx dy : ℝ)/denom=0
    simp [ticks,outside]
  · have small := lt_of_not_ge outside
    rw [if_neg (fun a => outside (hi.mp a))]
    let f := fun t : ℝ =>
      let a := tickDown (W.left t)
      let b := tickDown (W.left (t-tickUp y))
      min (2*a) (min (2*b) (a+b-tickUp x))
    have node (i : Fin 69) : f (gridY dy i) = (height dx dy (gridTick dy i.val):ℝ)/10^12 := by
      have b := gridTick_bounds dy hn small i.val
      exact height_eq W p dx dy _ b.1 b.2
    let term := fun i : Fin 68 =>
      areaDown ((gridY dy i.succ-gridY dy i.castSucc) *
        positiveChord (f (gridY dy i.castSucc)) (f (gridY dy i.succ)))
    have ht (i : Fin 68) : term i = (slab dx dy i.val:ℝ)/(2*10^24) := by
      dsimp only [term]
      rw [node,node]
      unfold slab gridY
      rw [← sub_div,← Int.cast_sub]
      exact segment_eq _ _ _
    change (ticks dx dy:ℝ)/(denom:ℝ) = (∑ i : Fin 68, term i)/(2*W.x*H)
    simp_rw [ht]
    rw [← Finset.sum_div,ticks_eq _ _ small,Int.cast_sum,p.1]
    norm_num [denom,PartialWave.xInt,PartialWave.scale,H]
    ring

theorem physical_sound (W : Datum) (p : Centres.partialProfile W) : holeEnclosure W physical := by
  intro x y v hx hy
  have y0 := (abs_nonneg _).trans hy
  rw [physical_eq_holeLower W p x y y0]
  apply holeLower_bound W x y _ _ v hx hy
  intro small
  apply grid_partition W p
  · exact Int.ceil_nonneg (by positivity)
  · rw [p.2.1] at small
    unfold tickUp at small
    rw [div_lt_iff₀ (by norm_num)] at small
    norm_num [cutoff,step] at small ⊢
    exact_mod_cast small

theorem physical_rat (x y : ℚ) : physical (x:ℝ) y = (overlap x y:ℝ) := by
  have ceil_eq (r : ℚ) : ⌈(r:ℝ)*10^12⌉ = (r*PartialWave.scale).ceil := by
    rw [show (r:ℝ)*10^12=((r*PartialWave.scale:ℚ):ℝ) by norm_num [PartialWave.scale],Rat.ceil_cast]
    rw [Rat.ceil_eq_neg_floor_neg]
    change ⌈r*PartialWave.scale⌉ = -⌊-(r*PartialWave.scale:ℚ)⌋
    simp only [Int.floor_neg,neg_neg]
  simp only [physical,overlap,ceil_eq,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_intCast]
  norm_num [denom,PartialWave.scale,PartialWave.xInt]

end
end HadwigerNelson.Certificate.Hole

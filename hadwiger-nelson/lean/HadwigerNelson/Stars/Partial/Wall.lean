import HadwigerNelson.Stars.Partial.Runtime
import HadwigerNelson.Wave.Geometry.Partial
import HadwigerNelson.Arithmetic.Rounding

/-! The integer interval used by the partial-wave classifier bounds the actual
profile at every integer ordinate, including both central plateaux. -/

namespace HadwigerNelson.Stars.PartialCheck
open Arithmetic Set

noncomputable def scaled (f : ℝ → ℝ) (y : ℝ) : ℝ := 10^12 * f (y/10^12)

private theorem lower_height (y : Int) (hl : 0 ≤ y) (hh : y ≤ 500000000000) :
    0 ≤ reflectedHeight y ∧ reflectedHeight y ≤ 250000000000 := by
  unfold reflectedHeight
  omega

private theorem scaled_reflect (f : ℝ → ℝ) (per : Function.Periodic f Wave.H)
    (even : ∀ t, f (-t) = f t) (y : Int) :
    scaled f y = scaled f (reflectedHeight y) := by
  unfold reflectedHeight
  rcases le_total y (500000000000-y) with h|h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    unfold scaled
    have eq : ((500000000000-y : Int):ℝ)/10^12 = Wave.H-(y:ℝ)/10^12 := by
      push_cast; norm_num [Wave.H]; ring
    rw [eq,per.sub_eq',even]

private theorem wallPair_spec (knot : Nat → Nat × Nat) (step y : Int) (hstep : 0 < step) :
    let i := (y/step).toNat
    let t : ℝ := ((y%step : Int):ℝ)/step
    let u : ℝ := (knot i).2
    let v : ℝ := (knot (i+1)).2
    (wallPair knot step y).1 ≤ (1-t)*u+t*v ∧ (1-t)*u+t*v ≤ (wallPair knot step y).2 := by
  dsimp only
  let w : Int := (knot (y/step).toNat).2
  let v : Int := (knot ((y/step).toNat+1)).2
  have id : (1-(↑(y%step):ℝ)/step)*(w:ℝ) + (↑(y%step):ℝ)/step*v =
      w+(((v-w)*(y%step):Int):ℝ)/step := by push_cast; ring
  change _ ≤ (1-(↑(y%step):ℝ)/step)*(w:ℝ) + (↑(y%step):ℝ)/step*v ∧
    (1-(↑(y%step):ℝ)/step)*(w:ℝ) + (↑(y%step):ℝ)/step*v ≤ _
  rw [id]
  by_cases hz : y%step = 0
  · simp [wallPair,hz,w]
  · simp only [wallPair,beq_iff_eq,hz,if_false]
    change ((w+(v-w)*(y%step)/step:Int):ℝ) ≤ _ ∧
      _ ≤ ((w+ceilDiv ((v-w)*(y%step)) step:Int):ℝ)
    rw [Int.cast_add,Int.cast_add]
    exact ⟨add_le_add_right (floorDiv_le_real _ hstep) _,add_le_add_right (real_le_ceilDiv _ hstep) _⟩

private theorem decomposition (y step : Int) (hy : 0 ≤ y) (hp : 0 < step) :
    let i := (y/step).toNat
    let t : ℝ := ((y%step:Int):ℝ)/step
    0 ≤ t ∧ t ≤ 1 ∧ (i+t)*step = (y:ℝ) := by
  have hq : 0 ≤ y/step := Int.ediv_nonneg hy hp.le
  have hr := Int.emod_nonneg y hp.ne'
  have hs := Int.emod_lt_of_pos y hp
  have whole := Int.emod_add_mul_ediv y step
  have sp : (0 : ℝ) < step := by exact_mod_cast hp
  have hcast : (((y/step).toNat:Nat):ℝ) = ((y/step:Int):ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hq
  refine ⟨div_nonneg (by exact_mod_cast hr) sp.le,(div_le_one sp).2 (by exact_mod_cast hs.le),?_⟩
  dsimp only
  rw [hcast,add_mul,div_mul_cancel₀ _ sp.ne']
  exact_mod_cast (by linarith only [whole] : y/step*step+y%step = y)

theorem right_integer (y : Int) (hy : 0 ≤ y) (hh : y ≤ 500000000000) :
    (right y).1 ≤ scaled PartialWave.datum.right y ∧ scaled PartialWave.datum.right y ≤ (right y).2 := by
  let v := reflectedHeight y
  let i := (v/976562500).toNat
  let t : ℝ := ((v%976562500:Int):ℝ)/976562500
  have lim := lower_height y hy hh
  have hi : i < 512 := by dsimp [i,v]; omega
  have ⟨t0,t1,atY⟩ := decomposition v 976562500 lim.1 (by decide)
  have atY' : ((i:ℝ)+t)*Wave.H/512 = (v:ℝ)/10^12 := by
    change ((i:ℝ)+t)*(976562500:ℝ) = (v:ℝ) at atY
    unfold Wave.H; linarith only [atY]
  have val := PartialWave.datum_right_segment ⟨i,hi⟩ t ⟨t0,t1⟩
  change PartialWave.datum.right (((i:ℝ)+t)*Wave.H/512) = _ at val
  rw [atY'] at val
  have lo := wallPair_spec PartialWave.rightKnot 976562500 v (by decide)
  have k (j : Nat) (hj : j < 513) : PartialWave.rightKnots[j]! = PartialWave.rightKnot j := by
    rw [getElem!_pos _ _ (by simpa [PartialWave.rightKnots] using hj),PartialWave.get_rightKnots j hj]
  rw [k _ (by omega),k _ (by omega)] at val
  rw [scaled_reflect _ PartialWave.datum.right_periodic PartialWave.datum.right_even y]
  change _ ≤ 10^12 * PartialWave.datum.right ((v:ℝ)/10^12) ∧
    10^12 * PartialWave.datum.right ((v:ℝ)/10^12) ≤ _
  rw [val]
  have cancel (u : ℝ) : 10^12*(u/10^12) = u := by ring
  rw [cancel]
  exact lo

theorem left_integer (y : Int) (hy : 0 ≤ y) (hh : y ≤ 500000000000) :
    (left y).1 ≤ scaled PartialWave.datum.left y ∧ scaled PartialWave.datum.left y ≤ (left y).2 := by
  let v := reflectedHeight y
  have lim := lower_height y hy hh
  rw [scaled_reflect _ PartialWave.datum.left_periodic PartialWave.datum.left_even y]
  by_cases flat : 9180000000 ≤ v
  · have vl : (9180000000:ℝ) ≤ v := by exact_mod_cast flat
    have vu : (v:ℝ) ≤ 250000000000 := by exact_mod_cast lim.2
    have w := PartialWave.datum.left_zero (v/10^12) (by
      rw [PartialWave.datum_y0]
      unfold Wave.H
      constructor <;> linarith)
    have z : left y = (0,0) := if_pos flat
    rw [z]
    simp [scaled,show reflectedHeight y = v from rfl,w]
  let i := (v/540000000).toNat
  let t : ℝ := ((v%540000000:Int):ℝ)/540000000
  have hi : i < 17 := by dsimp [i]; omega
  have ⟨t0,t1,atY⟩ := decomposition v 540000000 lim.1 (by decide)
  have atY' : ((i:ℝ)+t)*54/100000 = (v:ℝ)/10^12 := by
    change ((i:ℝ)+t)*(540000000:ℝ) = (v:ℝ) at atY
    linarith only [atY]
  have val := PartialWave.datum_left_segment ⟨i,hi⟩ t ⟨t0,t1⟩
  change PartialWave.datum.left (((i:ℝ)+t)*54/100000) = _ at val
  rw [atY'] at val
  have lo := wallPair_spec PartialWave.leftKnot 540000000 v (by decide)
  have k (j : Nat) (hj : j < 37) : PartialWave.leftKnots[j]! = PartialWave.leftKnot j := by
    rw [getElem!_pos _ _ (by simpa [PartialWave.leftKnots] using hj),PartialWave.get_leftKnots j hj]
  rw [k _ (by omega),k _ (by omega)] at val
  change (left y).1 ≤ 10^12 * PartialWave.datum.left ((v:ℝ)/10^12) ∧
    10^12 * PartialWave.datum.left ((v:ℝ)/10^12) ≤ (left y).2
  rw [val]
  have cancel (u : ℝ) : 10^12*(u/10^12)=u := by ring
  rw [cancel]
  simpa only [left, show ¬9180000000 ≤ reflectedHeight y from flat, if_false] using lo

end HadwigerNelson.Stars.PartialCheck

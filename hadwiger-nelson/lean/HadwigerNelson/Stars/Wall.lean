import HadwigerNelson.Stars.WaveClassifier
import HadwigerNelson.Angular.Datum
import HadwigerNelson.Angular.ScaledCell
import HadwigerNelson.Wave.Geometry.GridBounds

/-! Integer wall enclosures, unimodality, and the peak used by the checker
for the 2,049 actual knots of the complete-wave datum. -/

namespace HadwigerNelson.Stars.BoxCheck
open CompleteWave (height scale step profile ordinate rightAt)
open Set

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem rising_knots : ∀ i : Fin 1024, ordinate i ≤ ordinate (i.val+1) := by
  decide +kernel

private theorem half_interpolation (v : Nat → ℝ) {x : ℝ} (h : x ∈ Icc 0 1024) :
    Angular.Grid.interpolation v 2048 x = Angular.Grid.interpolation v 1024 x := by
  obtain ⟨i,hi,it⟩ := Angular.Grid.hasCell (n := 1024) (by decide) (by simpa using h)
  rw [Angular.Grid.interpolation_on v (n := 2048) (by omega : i < 2048) it,
    Angular.Grid.interpolation_on v hi it]

theorem rightAt_rising : MonotoneOn rightAt (Icc 0 (Wave.H/2)) := by
  intro a ha b hb hab
  let v (i : Nat) : ℝ := (ordinate i : ℝ)/scale
  have mono := Angular.Grid.interpolation_mono v 1024 (by
    intro i hi
    exact div_le_div_of_nonneg_right (by exact_mod_cast rising_knots ⟨i,hi⟩)
      (by positivity))
  have bound (z : ℝ) (hz : z ∈ Icc 0 (Wave.H/2)) : 4096*z ∈ Icc 0 1024 := by
    obtain ⟨l,h⟩ := hz
    unfold Wave.H at h
    constructor <;> linarith
  change Angular.Grid.interpolation v 2048 (4096*a) ≤ Angular.Grid.interpolation v 2048 (4096*b)
  rw [half_interpolation v (bound _ ha),half_interpolation v (bound _ hb)]
  exact mono (by linarith)

private theorem wall_at {t : ℝ} (ht : t ∈ Icc 0 (height : ℝ)) :
    scaledWall Wave.completeDatum t = (scale : ℝ)*rightAt (t/scale) := by
  unfold scaledWall
  rw [Wave.completeDatum_right]
  constructor
  · exact div_nonneg ht.1 (by norm_num [scale])
  · have h := ht.2
    norm_num [height,scale] at h
    norm_num [scale,Wave.H]
    linarith

theorem scaledWall_rising : MonotoneOn (scaledWall Wave.completeDatum) (Icc 0 ((height : ℝ)/2)) := by
  intro a ha b hb h
  have H (x : ℝ) (hx : x ∈ Icc 0 ((height : ℝ)/2)) :
      x ∈ Icc 0 (height : ℝ) ∧ x/(scale : ℝ) ∈ Icc 0 (Wave.H/2) := by
    obtain ⟨l,r⟩ := hx
    norm_num [scale,height,Wave.H] at r ⊢
    exact ⟨⟨l,by linarith⟩,by linarith,by linarith⟩
  rw [wall_at (H _ ha).1,wall_at (H _ hb).1]
  exact mul_le_mul_of_nonneg_left (rightAt_rising (H _ ha).2 (H _ hb).2
    (div_le_div_of_nonneg_right h (by positivity))) (by positivity)

private theorem wall_reflected {x : ℝ} (hx : x ∈ Icc 0 (height : ℝ)) :
    scaledWall Wave.completeDatum ((height : ℝ)-x) = scaledWall Wave.completeDatum x := by
  rw [wall_at ⟨by linarith [hx.2],by linarith [hx.1]⟩,wall_at hx]
  have id : ((height : ℝ)-x)/scale = Wave.H-x/scale := by norm_num [height,scale,Wave.H]; ring
  rw [id,CompleteWave.rightAt_reflect]
  obtain ⟨l,r⟩ := hx
  constructor <;> norm_num [height,scale,Wave.H] at r ⊢ <;> linarith

theorem scaledWall_falling :
    AntitoneOn (scaledWall Wave.completeDatum) (Icc ((height : ℝ)/2) height) := by
  intro a ha b hb h
  have pos : (0 : ℝ) ≤ (height : ℝ)/2 := by norm_num [height,scale]
  have a0 : a ∈ Icc 0 (height : ℝ) := ⟨pos.trans ha.1,ha.2⟩
  have b0 : b ∈ Icc 0 (height : ℝ) := ⟨pos.trans hb.1,hb.2⟩
  rw [←wall_reflected b0,←wall_reflected a0]
  apply scaledWall_rising
  · exact ⟨by linarith [hb.2],by linarith [hb.1]⟩
  · exact ⟨by linarith [ha.2],by linarith [ha.1]⟩
  · linarith

private theorem step_bounds (i : Nat) (hi : i ≤ 2048) :
    ((i*step : Nat) : ℝ) ∈ Icc 0 (height : ℝ) := by
  have h : (i : ℝ) ≤ 2048 := by exact_mod_cast hi
  norm_num [height,step,scale]
  linarith

private theorem wall_knot (i : Nat) (hi : i ≤ 2048) :
    scaledWall Wave.completeDatum (i*step : Nat) = ((profile[i]?.getD 0 : Nat) : ℝ) := by
  rw [wall_at (step_bounds i hi)]
  by_cases last : i = 2048
  · subst i
    have h := Angular.scaled_on_cell 2047 (by decide) (z := (2048*step : Nat))
      ⟨by norm_num [step],le_rfl⟩
    rw [show 2047+1 = 2048 by rfl, Arithmetic.linearAt_right _ _ (by norm_num [step])] at h
    exact h
  · have h := Angular.scaled_on_cell i (by omega) (z := (i*step : Nat))
      ⟨le_rfl,by exact_mod_cast Nat.mul_le_mul_right step (Nat.le_succ i)⟩
    simpa only [Arithmetic.linearAt_left] using h

private theorem wall_integer (j : Int) (hj : 0 ≤ j) (hb : j ≤ height) :
    ((wall j).1 : ℝ) ≤ scaledWall Wave.completeDatum j ∧
    scaledWall Wave.completeDatum j ≤ (wall j).2 := by
  let i := (j/(step : Int)).toNat
  let r := j%(step : Int)
  let a : Int := (profile[i]?.getD 0 : Nat)
  let b : Int := (profile[i+1]?.getD 0 : Nat)
  have r0 : 0 ≤ r := Int.emod_nonneg _ (by decide)
  have rs : r < step := Int.emod_lt_of_pos _ (by decide)
  have eqi : (i : Int) = j/(step : Int) := Int.toNat_of_nonneg (Int.ediv_nonneg hj (by decide))
  have split : j = (i : Int)*step+r := by
    rw [eqi]
    exact (Int.ediv_mul_add_emod j step).symm
  have hi : i ≤ 2048 := by
    norm_num [height,scale] at hb
    norm_num [step] at split
    omega
  have rel : (j : ℝ) = ((i*step : Nat):ℝ)+r := by exact_mod_cast split
  change ((if r = 0 then (a,a) else (a+(b-a)*r/step,a+Arithmetic.ceilDiv ((b-a)*r) step) : Int × Int).1 : ℝ) ≤ _ ∧ _ ≤
    ((if r = 0 then (a,a) else (a+(b-a)*r/step,a+Arithmetic.ceilDiv ((b-a)*r) step) : Int × Int).2 : ℝ)
  by_cases h : r = 0
  · simp only [if_pos h]
    rw [rel,h,Int.cast_zero,add_zero,wall_knot _ hi]
    exact ⟨le_rfl,le_rfl⟩
  simp only [if_neg h,Int.cast_add]
  have ii : i < 2048 := by
    norm_num [height,scale] at hb
    norm_num [step] at split
    omega
  have cell : (j:ℝ) ∈ Icc ((i*step : Nat) : ℝ) (((i+1)*step : Nat) : ℝ) := by
    rw [rel]
    obtain ⟨hr0,hrs⟩ : (0:ℝ) ≤ r ∧ (r:ℝ) < step := ⟨by exact_mod_cast r0,by exact_mod_cast rs⟩
    push_cast
    constructor <;> nlinarith
  have y0 : (j : ℝ) ∈ Icc 0 (height : ℝ) := ⟨by exact_mod_cast hj,by exact_mod_cast hb⟩
  have val : scaledWall Wave.completeDatum j = (a : ℝ)+((b:ℝ)-a)*r/step := by
    rw [wall_at y0,Angular.scaled_on_cell i ii cell]
    unfold Arithmetic.linearAt
    rw [rel]
    push_cast
    dsimp [a,b]
    norm_num [step]
    ring
  rw [val]
  have hl := Arithmetic.floorDiv_le_real ((b-a)*r) (b := (step : Int)) (by decide)
  have hu := Arithmetic.real_le_ceilDiv ((b-a)*r) (b := (step : Int)) (by decide)
  push_cast at hl hu
  exact ⟨add_le_add_right hl _,add_le_add_right hu _⟩

theorem completeWallBounds : WallBounds (scaledWall Wave.completeDatum) where
  low := fun j hj hb => (wall_integer j hj hb).1
  high := fun j hj hb => (wall_integer j hj hb).2
  rising := scaledWall_rising
  falling := scaledWall_falling
  maximum := by
    have h := wall_knot 1024 (by decide)
    rw [show (height : ℝ)/2 = ((1024*step : Nat) : ℝ) by norm_num [height,scale,step],h]
    exact le_rfl

end HadwigerNelson.Stars.BoxCheck

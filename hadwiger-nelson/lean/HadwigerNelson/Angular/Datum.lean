import HadwigerNelson.Angular.GridRational
import HadwigerNelson.Angular.Profile
import HadwigerNelson.Angular.ProfileCheck
import HadwigerNelson.Wave.Geometry.Interval

namespace HadwigerNelson.CompleteWave
open HadwigerNelson.Angular.Grid
open HadwigerNelson.Wave

private def ordinateQ (i : Nat) : ℚ := (ordinate i : ℚ)/scale

theorem rightAt_rational : RationalProfile rightAt := by
  have h := rationalProfile ordinateQ 2048 (by decide)
  simpa only [rightAt,ordinateQ,Rat.cast_div,Rat.cast_natCast,Nat.cast_ofNat,
    show (2:ℝ)*2048 = 4096 by norm_num] using h

theorem rightAt_reflect {y : ℝ} (hy : y ∈ Set.Icc 0 H) : rightAt (H-y) = rightAt y := by
  have up : 4096*y ≤ 2048 := by have := hy.2; unfold H at this; linarith
  have base := reflect (fun i => (ordinate i : ℝ)/scale) 2048 (by decide)
    (by intro i hi; simp only [(ordinate_facts validProfile hi).2.2.1])
    (u := 4096*y) ⟨mul_nonneg (by norm_num) hy.1,up⟩
  have e : 4096*(H-y) = 2048-4096*y := by unfold H; ring
  simpa only [rightAt,e,Nat.cast_ofNat] using base

theorem rightAt_complement {y : ℝ} (hy : y ∈ Set.Icc 0 (H/2)) :
    rightAt y + rightAt (y+H/2) = 2*((xInt:ℝ)/scale) := by
  have up : 4096*y ≤ 1024 := by have := hy.2; unfold H at this; linarith
  have base := complement (fun i => (ordinate i : ℝ)/scale) 1024 (2*((xInt:ℝ)/scale))
    (by decide) (by
      intro i hi
      have e := (ordinate_facts validProfile (by omega : i ≤ 2048)).2.2.2 hi
      have e' : (ordinate i : ℝ) + ordinate (i+1024) = 2*xInt := by exact_mod_cast e
      rw [←add_div,e']
      ring) (u := 4096*y) ⟨mul_nonneg (by norm_num) hy.1,up⟩
  have e : 4096*(y+H/2) = 4096*y+1024 := by unfold H; ring
  simpa only [rightAt,e,Nat.cast_ofNat] using base

theorem rightAt_bounds {y : ℝ} (hy : y ∈ Set.Icc 0 H) : 4/5 < rightAt y ∧ rightAt y < 1 := by
  have up : 4096*y ≤ 2048 := by have := hy.2; unfold H at this; linarith
  apply between _ (by decide : 0 < 2048) _ ⟨mul_nonneg (by norm_num) hy.1,up⟩
  intro i hi
  have v := ordinate_facts validProfile hi
  have low : (4:ℝ)*scale < 5*(ordinate i : ℝ) := by exact_mod_cast v.1
  have high : (ordinate i : ℝ) < scale := by exact_mod_cast v.2.1
  have pos : (0:ℝ) < scale := by norm_num [scale]
  constructor
  · apply (lt_div_iff₀ pos).2
    linarith
  · exact (div_lt_one pos).2 high

end HadwigerNelson.CompleteWave

namespace HadwigerNelson.Wave

private theorem exists_completeDatum :
    ∃ W : Datum, W.x=(CompleteWave.xInt:ℝ)/CompleteWave.scale ∧
      W.left=(fun _ => 0) ∧ W.y0=0 ∧ Set.EqOn W.right CompleteWave.rightAt (Set.Icc 0 H) := by
  let x : ℚ := (CompleteWave.xInt : ℚ)/CompleteWave.scale
  have h := complete_of_interval x _ (by norm_num [x,CompleteWave.scale,CompleteWave.xInt])
    CompleteWave.rightAt_rational CompleteWave.rightAt_continuous.continuousOn
    (fun _ => CompleteWave.rightAt_reflect) (fun y hy => by
      simpa [x] using CompleteWave.rightAt_complement hy) (fun _ => CompleteWave.rightAt_bounds)
  simpa [x] using h

/-- The complete edge wave with the specified published rational boundary table. -/
noncomputable def completeDatum : Datum := exists_completeDatum.choose

theorem completeDatum_x : completeDatum.x = (CompleteWave.xInt:ℝ)/CompleteWave.scale :=
  exists_completeDatum.choose_spec.1

theorem completeDatum_left (y : ℝ) : completeDatum.left y = 0 :=
  congrFun exists_completeDatum.choose_spec.2.1 y

theorem completeDatum_y0 : completeDatum.y0 = 0 := exists_completeDatum.choose_spec.2.2.1

theorem completeDatum_right : Set.EqOn completeDatum.right CompleteWave.rightAt (Set.Icc 0 H) :=
  exists_completeDatum.choose_spec.2.2.2

end HadwigerNelson.Wave

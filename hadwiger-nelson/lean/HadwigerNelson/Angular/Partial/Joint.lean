import HadwigerNelson.Angular.Partial.Runtime
import HadwigerNelson.Arithmetic.Positive

namespace HadwigerNelson.Angular.Partial
open Arithmetic Set MeasureTheory

noncomputable def value (s : Segment) (z : ℝ) : ℝ :=
  linearAt s.start s.left s.stop s.right z

private theorem gapUpper_sound (r l : Segment) (d : Int) (z : Nat)
    (hr : r.start<r.stop) (hl : l.start<l.stop) :
    value r z - value l z - d ≤ (gapUpper r l d z:ℝ) := by
  have ht := interpUp_spec r.start r.left r.stop r.right (z:Int) hr
  have hb := interpDown_spec l.start l.left l.stop l.right (z:Int) hl
  simp only [Int.cast_natCast] at ht hb
  simp only [value,gapUpper,Int.cast_sub]
  linarith only [ht,hb]

private theorem value_cont (s : Segment) : Continuous (value s) := by
  unfold value linearAt
  fun_prop

private theorem interpolate_diff (a b d u v s t z : ℝ) :
    linearAt a u b v z - linearAt a s b t z - d =
      linearAt a (u-s-d) b (v-t-d) z := by
  unfold linearAt
  ring

/-- The doubled integral on any common affine piece is bounded by outward
rounding at its two endpoints and integrating their positive part. -/
theorem joint_integral_le (r l : Segment) (d : Int) (a b : Nat)
    (hr : r.start<r.stop) (hl : l.start<l.stop) (hab : a≤b) :
    2*(∫ z in (a:ℝ)..(b:ℝ), max 0 (value r z-value l z-d)) ≤
      (jointArea r l d a b:ℝ) := by
  rcases hab.eq_or_lt with eq|lt
  · subst b
    simp [jointArea]
  let u := gapUpper r l d a
  let v := gapUpper r l d b
  have abr : (a:ℝ)<b := by exact_mod_cast lt
  have zbound (z : ℝ) (hz : z∈Icc (a:ℝ) (b:ℝ)) :
      value r z - value l z - d ≤ linearAt a u b v z := by
    have chk (s : Segment) (hs : s.start<s.stop) :
        linearAt a (value s a) b (value s b) z = value s z :=
      linearAt_restrict _ _ _ (by exact_mod_cast hs) abr
    rw [←chk r hr, ←chk l hl,interpolate_diff]
    exact linearAt_mono abr hz.1 hz.2 (gapUpper_sound r l d a hr hl) (gapUpper_sound r l d b hr hl)
  have major := intervalIntegral.integral_mono_on (μ:=volume) abr.le
    ((continuous_const.max (((value_cont r).sub (value_cont l)).sub continuous_const)).intervalIntegrable _ _)
    (show IntervalIntegrable (fun z : ℝ => max 0 (linearAt a u b v z)) volume a b from by
      apply Continuous.intervalIntegrable
      unfold linearAt
      fun_prop)
    (fun z hz => max_le_max_left 0 (zbound z hz))
  have leaf := integral_positive_linearAt_le (a:Int) (b:Int) u v (by exact_mod_cast lt)
  simp only [Int.cast_natCast] at leaf
  apply (mul_le_mul_of_nonneg_left major (by norm_num : (0:ℝ)≤2)).trans
  apply leaf.trans
  simp only [jointArea,if_pos lt]
  exact_mod_cast Int.self_le_toNat _

end HadwigerNelson.Angular.Partial

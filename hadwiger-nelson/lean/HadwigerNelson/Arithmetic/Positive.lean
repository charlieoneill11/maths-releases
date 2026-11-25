import HadwigerNelson.Arithmetic.Interpolation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp

/-! Exact area under the positive part of an affine segment, including an interior zero. -/

open MeasureTheory Set

namespace HadwigerNelson.Arithmetic

private theorem integral_affine (u s a b : ℝ) :
    (∫ t in a..b, u + s*t) = (b-a)*u + s*((b^2-a^2)/2) := by
  let f (t : ℝ) := u+s*t
  have hr : (∫ t in a..b, f (a+b-t)) = ∫ t in a..b, f t := by
    simp
  have havg : (∫ t in a..b, f t)+(∫ t in a..b, f (a+b-t)) = (b-a)*(2*u+s*(a+b)) := by
    calc
      _ = ∫ t in a..b, f t+f (a+b-t) := by
        apply (intervalIntegral.integral_add ?_ ?_).symm <;>
          apply Continuous.intervalIntegrable <;> dsimp [f] <;> fun_prop
      _ = ∫ _t in a..b, 2*u+s*(a+b) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp [f]
        ring
      _ = _ := by rw [intervalIntegral.integral_const,smul_eq_mul]
  rw [hr] at havg
  dsimp [f] at havg
  linarith only [havg]

private theorem integral_positive_unit_sorted (u v : ℝ) (huv : u ≤ v) :
    2 * (∫ t in (0:ℝ)..1, max 0 (u + (v-u)*t)) = positiveArea2 u v 1 := by
  simp only [positiveArea2, min_eq_left huv, max_eq_right huv]
  have hs : 0 ≤ v-u := sub_nonneg.mpr huv
  have zero_on (a b : ℝ) (hab : a ≤ b) (hb : u + (v-u)*b ≤ 0) :
      (∫ t in a..b, max 0 (u+(v-u)*t)) = 0 := by
    calc
      _ = ∫ _t in a..b, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hab] at ht
        exact max_eq_left (by linarith [mul_le_mul_of_nonneg_left ht.2 hs])
      _ = 0 := by simp
  have pos_on (a b : ℝ) (hab : a ≤ b) (ha : 0 ≤ u + (v-u)*a) :
      (∫ t in a..b, max 0 (u+(v-u)*t)) = (b-a)*u + (v-u)*((b^2-a^2)/2) := by
    calc
      _ = ∫ t in a..b, u+(v-u)*t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hab] at ht
        exact max_eq_right (by linarith [mul_le_mul_of_nonneg_left ht.1 hs])
      _ = _ := integral_affine _ _ _ _
  split_ifs with hv hu
  · rw [zero_on 0 1 zero_le_one (by linarith)]
    ring
  · rw [pos_on 0 1 zero_le_one (by linarith)]
    ring
  · have hs' : 0 < v-u := by linarith
    let z := -u/(v-u)
    have hroot : (v-u)*z = -u := by dsimp [z]; field_simp
    have hz0 : 0 ≤ z := div_nonneg (by linarith) hs'.le
    have hz1 : z ≤ 1 := (div_le_iff₀ hs').2 (by linarith)
    have hf : Continuous (fun t : ℝ => max 0 (u+(v-u)*t)) :=
      continuous_const.max (continuous_const.add (continuous_const.mul continuous_id))
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (a := 0) (b := z)) (hf.intervalIntegrable (a := z) (b := 1)),
      zero_on 0 z hz0 (by linarith), pos_on z 1 hz1 (by linarith)]
    dsimp [z]
    field_simp [ne_of_gt hs']
    ring

private theorem integral_positive_unit (u v : ℝ) :
    2 * (∫ t in (0:ℝ)..1, max 0 (u + (v-u)*t)) = positiveArea2 u v 1 := by
  rcases le_total u v with huv | hvu
  · exact integral_positive_unit_sorted u v huv
  · have hsymm : (∫ t in (0:ℝ)..1, max 0 (u+(v-u)*t)) =
        ∫ t in (0:ℝ)..1, max 0 (v+(u-v)*t) := by
      calc
        _ = ∫ t in (0:ℝ)..1, max 0 (v+(u-v)*(1-t)) := by
          apply intervalIntegral.integral_congr
          intro t _
          apply congrArg (max (0:ℝ))
          ring
        _ = _ := by
          simpa using intervalIntegral.integral_comp_sub_left (a := 0) (b := 1)
            (fun t : ℝ => max 0 (v+(u-v)*t)) 1
    rw [hsymm, integral_positive_unit_sorted v u hvu]
    simp only [positiveArea2, min_comm v u, max_comm v u]

/-- Twice the integral in the same units as the horizontal width times the two endpoint values. -/
theorem integral_positive_linearAt (l r u v : ℝ) (hlr : l < r) :
    2 * (∫ z in l..r, max 0 (linearAt l u r v z)) = positiveArea2 u v (r-l) := by
  have hwidth : r-l ≠ 0 := ne_of_gt (sub_pos.mpr hlr)
  have hchange : (r-l)*(∫ t in (0:ℝ)..1, max 0 (u+(v-u)*t)) =
      ∫ z in l..r, max 0 (linearAt l u r v z) := by
    calc
      _ = (r-l)*(∫ t in (0:ℝ)..1, max 0 (linearAt l u r v ((r-l)*t+l))) := by
        congr 1
        apply intervalIntegral.integral_congr
        intro t _
        apply congrArg (max (0:ℝ))
        dsimp [linearAt]
        field_simp
        ring
      _ = _ := by
        simpa [smul_eq_mul] using intervalIntegral.smul_integral_comp_mul_add (a := 0) (b := 1)
          (fun z : ℝ => max 0 (linearAt l u r v z)) (r-l) l
  rw [← hchange, mul_left_comm, integral_positive_unit]
  dsimp only [positiveArea2]
  split_ifs <;> ring

/-- Sound integer result for every leaf of the positive-overlap integration. -/
theorem integral_positive_linearAt_le (l r u v : Int) (hlr : l < r) :
    2 * (∫ z in (l:ℝ)..(r:ℝ), max 0 (linearAt l u r v z)) ≤
      (positiveArea2Up u v (r-l) : ℝ) := by
  rw [integral_positive_linearAt _ _ _ _ (by exact_mod_cast hlr)]
  simpa using positiveArea2Up_spec u v (r-l)

/-- The partly retained leaf rounds its new left endpoint upwards before integration. -/
theorem integral_clipped_linearAt_le (l r u v d s : Int) (hlr : l < r) (hsr : s < r) :
    2 * (∫ z in (s:ℝ)..(r:ℝ), max 0 (linearAt l u r v z - d)) ≤
      (positiveArea2Up (interpUp l u r v s - d) (v-d) (r-s) : ℝ) := by
  let a := interpUp l u r v s - d
  let b := v-d
  have hsr' : (s:ℝ) < r := by exact_mod_cast hsr
  apply le_trans _ (integral_positive_linearAt_le s r a b hsr)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply intervalIntegral.integral_mono_on hsr'.le
  · apply Continuous.intervalIntegrable
    unfold linearAt
    fun_prop
  · apply Continuous.intervalIntegrable
    unfold linearAt
    fun_prop
  · intro z hz
    apply max_le_max_left
    dsimp only [a,b]
    push_cast
    exact linearAt_clipped_upper l r u v d s hlr hsr hz.1 hz.2

/-- Converting fixed-point overlap to physical area scales both coordinates.
The horizontal cut d is in integer ticks. -/
theorem integral_scaled_positive (f : ℝ → ℝ) (l r d S : ℝ) (hS : 0 < S) :
    (∫ z in l..r, max 0 (S*f (z/S)-d)) =
      S^2 * (∫ y in l/S..r/S, max 0 (f y-d/S)) := by
  let g (y : ℝ) := max 0 (f y-d/S)
  have hcut : S*(d/S) = d := by field_simp
  calc
    _ = ∫ z in l..r, S*g (z/S) := by
      apply intervalIntegral.integral_congr
      intro z _
      simp only [g,mul_max_of_nonneg _ _ hS.le,mul_zero,mul_sub,hcut]
    _ = S * (S * (∫ y in l/S..r/S, g y)) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_div g hS.ne',smul_eq_mul]
    _ = _ := by dsimp only [g]; ring

end HadwigerNelson.Arithmetic

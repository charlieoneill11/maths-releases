import HadwigerNelson.Angular.Partial.Cells
import HadwigerNelson.Angular.Integral
import HadwigerNelson.Angular.Bins
import HadwigerNelson.Angular.Range
import HadwigerNelson.Placement.Slice

namespace HadwigerNelson.Angular.Partial
open Arithmetic Set MeasureTheory

noncomputable def rightGap (W : Wave.Datum) (d : Int) (z : ℝ) :=
  max 0 (S*W.right (z/S)-d)

noncomputable def fullGap (W : Wave.Datum) (d : Int) (lo : Nat) (hi z : ℝ) :=
  max 0 (S*(W.right (z/S) - W.left (Placement.closestHeight Wave.H ((lo:ℝ)/S) hi (z/S)))-d)

private theorem rightGap_cont (W : Wave.Datum) (d : Int) : Continuous (rightGap W d) := by
  unfold rightGap
  have hr := W.right_continuous
  fun_prop

private theorem fullGap_cont (W : Wave.Datum) (d : Int) (lo : Nat) (hi : ℝ) :
    Continuous (fullGap W d lo hi) := by
  unfold fullGap Placement.closestHeight
  have hr := W.right_continuous
  have hl := W.left_continuous
  fun_prop

private theorem full_le_right (W : Wave.Datum) (d : Int) (lo : Nat) (hi : ℝ)
    {a b : ℝ} (hab : a≤b) :
    (∫ z in a..b, fullGap W d lo hi z) ≤ ∫ z in a..b, rightGap W d z := by
  apply intervalIntegral.integral_mono_on hab ((fullGap_cont ..).intervalIntegrable _ _)
    ((rightGap_cont ..).intervalIntegrable _ _)
  intro z _
  apply max_le_max_left
  apply sub_le_sub_right
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (W.left_bounds _).1) (by norm_num [S])

private theorem right_bound {W : Wave.Datum} (p : Profile W) (d : Int) (a : Nat) (ha : a≤height) :
    2*(∫ z in (a:ℝ)..(height:ℝ), rightGap W d z) ≤ (walls.tree.fastArea d a:ℝ) := by
  let f := fun z : ℝ => S*W.right (z/S)
  have hf : Continuous f := continuous_const.mul (W.right_continuous.comp (continuous_id.div_const _))
  have h := tabulate_integral_le rightValues rightStep (by decide) f hf d a 9 0 (by
    intro q _ hq z hz
    have e := p.right_value q (by omega) hz
    simpa only [f,value,rightSegment,walls,Int.cast_mul,Int.cast_add,Int.cast_one,Int.cast_natCast,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using e)
  have eh : (0+2^9)*rightStep = height := by decide
  simp only [Nat.zero_mul,Nat.cast_zero,Int.cast_natCast,max_eq_right (Nat.cast_nonneg a),eh,
    max_eq_left (by exact_mod_cast ha : (a:ℝ)≤height)] at h
  have ok : walls.tree.Valid := tabulate_valid _ _ (by decide) _ _
  rw [walls.tree.fastArea_eq ok]
  exact h

private theorem near_bound {W : Wave.Datum} (p : Profile W) (d : Int) (lo : Nat)
    (hlo : lo≤height) :
    2*(∫ z in (lo:ℝ)..(↑(min height (lo+cutoff)):ℝ), nearGap W d lo z) ≤
      (rangeSum (rowArea walls d lo) 0 17 : ℝ) := by
  let e (i : Nat) : ℝ := ↑(min height (lo+i*leftStep))
  have sy := intervalIntegral.sum_integral_adjacent_intervals (μ:=volume) (n:=17)
    (a:=e) (fun i _ => (nearGap_cont W d lo).intervalIntegrable (e i) (e (i+1)))
  have e0 : e 0 = lo := by simp only [e,Nat.zero_mul,Nat.add_zero,min_eq_right hlo]
  have e17 : e 17 = ↑(min height (lo+cutoff)) := rfl
  rw [←e0,←e17,←sy,Finset.mul_sum,rangeSum_spec,Nat.cast_sum]
  simp only [Nat.zero_add]
  apply Finset.sum_le_sum
  intro i h
  exact row_bound p d lo i (Finset.mem_range.mp h)

/-- In the first 0.00918 height units the closest height gives exactly
the translated lower wall. Beyond this band all left-wall values are
nonnegative, and dropping the wall gives a valid upper enclosure. -/
private theorem integrated_slice {W : Wave.Datum} (p : Profile W) (d : Int) (lo : Nat) (hi : ℝ)
    (hlo : lo<height) (span : (lo:ℝ)/S≤hi) :
    2*(∫ z in (lo:ℝ)..(height:ℝ), fullGap W d lo hi z) ≤ (slice walls d lo:ℝ) := by
  let m := min height (lo+cutoff)
  have upper : m≤height := min_le_left ..
  have lower : lo≤m := le_min hlo.le (Nat.le_add_right ..)
  have ok : walls.tree.Valid := tabulate_valid _ _ (by decide) _ _
  unfold slice
  simp only [Int.toNat_natCast]
  split_ifs with empty
  · simp only [Bool.or_eq_true,decide_eq_true_eq] at empty
    have sk := empty.resolve_right (by omega)
    have h := right_bound p d lo hlo.le
    rw [Segments.fastArea_eq _ ok,Segments.area_eq_zero_of_misses _ ok sk le_rfl le_rfl] at h
    apply le_trans (mul_le_mul_of_nonneg_left (full_le_right W d lo hi (by exact_mod_cast hlo.le : (lo:ℝ)≤height)) (by norm_num))
    simpa using h
  · have close : (∫ z in (lo:ℝ)..(m:ℝ), fullGap W d lo hi z) =
        ∫ z in (lo:ℝ)..(m:ℝ), nearGap W d lo z := by
      apply intervalIntegral.integral_congr
      intro z hz
      rw [uIcc_of_le (by exact_mod_cast lower)] at hz
      have bound : m ≤ lo+cutoff := min_le_right ..
      have r : z≤(lo:ℝ)+cutoff := hz.2.trans (by exact_mod_cast bound)
      have act : z/S - (lo:ℝ)/S ≤ 17*540000000/(10:ℝ)^12 := by
        rw [←sub_div]; apply div_le_div_of_nonneg_right _ (by norm_num [S]); apply sub_le_iff_le_add'.mpr; simpa only [cutoff,leftStep,Nat.cast_mul,Nat.cast_ofNat] using r
      simp only [fullGap,nearGap,closestHeight_left W span act,sub_div,mul_sub]
    have far : 2*(∫ z in (m:ℝ)..(height:ℝ), fullGap W d lo hi z) ≤
        ((walls.tree.fastArea d (lo+cutoff:Nat)).toNat:ℝ) := by
      by_cases ht : height≤lo+cutoff
      · have e : m=height := min_eq_left ht
        rw [e,intervalIntegral.integral_same,mul_zero]
        exact Nat.cast_nonneg _
      · have e : m=lo+cutoff := min_eq_right (by omega)
        have h := right_bound p d m upper
        have a := full_le_right W d lo hi (by exact_mod_cast upper : (m:ℝ)≤height)
        apply ((mul_le_mul_of_nonneg_left a (by norm_num : (0:ℝ)≤2)).trans h).trans
        rw [e]
        exact_mod_cast Int.self_le_toNat _
    have joined := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
      ((fullGap_cont W d lo hi).intervalIntegrable (lo:ℝ) (m:ℝ))
      ((fullGap_cont W d lo hi).intervalIntegrable (m:ℝ) (height:ℝ))
    rw [←joined,mul_add,close,Nat.cast_add]
    exact add_le_add (near_bound p d lo hlo.le) far

theorem slice_bound {W : Wave.Datum} (p : Profile W) (d lo : Int) (hi : ℝ)
    (hlo : 0≤lo) (span : (lo:ℝ)/S ≤ hi) :
    Placement.sliceUpper W.left W.right Wave.H ((d:ℝ)/S) ((lo:ℝ)/S) hi ≤
      (slice walls d lo:ℝ)/(2*S^2) := by
  let n := lo.toNat
  have en : (n:Int)=lo := Int.toNat_of_nonneg hlo
  have er : (n:ℝ)=(lo:ℝ) := by exact_mod_cast en
  have hheight : (height:ℝ)/S=Wave.H := by norm_num [height,S,Wave.H]
  unfold Placement.sliceUpper
  split_ifs with far
  · positivity
  · have hl : n<height := by
      have h : (n:ℝ)/S < (height:ℝ)/S := by rw [er,hheight]; exact lt_of_not_ge far
      exact_mod_cast (div_lt_div_iff_of_pos_right (by norm_num [S] : (0:ℝ)<S)).1 h
    let f := fun y => W.right y-W.left (Placement.closestHeight Wave.H ((n:ℝ)/S) hi y)
    have up := integrated_slice p d n hi hl (by rwa [er])
    have conv := integral_scaled_positive f (n:ℝ) (height:ℝ) (d:ℝ) S (by norm_num [S])
    change 2*(∫ z in (n:ℝ)..(height:ℝ), max 0 (S*f (z/S)-d)) ≤ _ at up
    rw [conv] at up
    dsimp only [f] at up
    rw [er,hheight,en] at up
    apply (le_div_iff₀ (by norm_num [S])).2
    linarith only [up]

end HadwigerNelson.Angular.Partial

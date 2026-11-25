import HadwigerNelson.Angular.Partial.Profile
import HadwigerNelson.Angular.Partial.Joint

namespace HadwigerNelson.Angular.Partial
open Arithmetic Set MeasureTheory

abbrev S : ℝ := 10^12

private theorem right_entry (q : Nat) (h : q<513) :
    rightValues[q]?.getD 0 = (PartialWave.rightKnot q).2 := by
  simp [rightValues,PartialWave.rightKnots,h]

private theorem left_entry (q : Nat) (h : q<37) :
    leftValues[q]?.getD 0 = (PartialWave.leftKnot q).2 := by
  simp [leftValues,PartialWave.leftKnots,h]

theorem Profile.right_value {W : Wave.Datum} (p : Profile W) (q : Nat) (hq : q<512)
    {z : ℝ} (hz : z ∈ Icc (↑(q*rightStep):ℝ) (↑((q+1)*rightStep):ℝ)) :
    S*W.right (z/S) = value (rightSegment walls q) z := by
  rw [p.right_cell q hq (by simpa using hz)]
  simp [value,rightSegment,walls,scaledRight,rightStep,right_entry q (by omega),right_entry (q+1) (by omega)]

theorem Profile.left_value {W : Wave.Datum} (p : Profile W) (lo i : Nat) (hi : i<17)
    {z : ℝ} (hz : z ∈ Icc (↑(lo+i*leftStep):ℝ) (↑(lo+(i+1)*leftStep):ℝ)) :
    S*W.left ((z-lo)/S) = value (foldedSegment walls lo i) z := by
  have h' : z-(lo:ℝ) ∈ Icc ((i:ℝ)*540000000) (((i:ℝ)+1)*540000000) := by
    obtain ⟨l,u⟩ := hz
    push_cast at l u
    exact ⟨by linarith [l],by linarith [u]⟩
  rw [p.left_cell i hi h']
  simp [value,foldedSegment,walls,scaledLeft,leftStep,left_entry i (by omega),left_entry (i+1) (by omega),linearAt]
  ring

/-- Integrand of twice-area evaluation in integer-length units on the
translated lower-wall band. -/
noncomputable def nearGap (W : Wave.Datum) (d : Int) (lo : Nat) (z : ℝ) : ℝ :=
  max 0 (S*W.right (z/S) - S*W.left ((z-lo)/S) - d)

theorem nearGap_cont (W : Wave.Datum) (d : Int) (lo : Nat) : Continuous (nearGap W d lo) := by
  unfold nearGap
  have hr := W.right_continuous
  have hl := W.left_continuous
  fun_prop

private theorem cell_bound {W : Wave.Datum} (p : Profile W) (d : Int) (lo i q a b : Nat)
    (hi : i<17) (hq : q<512) (hab : a≤b)
    (la : lo+i*leftStep ≤ a) (lb : b ≤ lo+(i+1)*leftStep)
    (ra : q*rightStep ≤ a) (rb : b ≤ (q+1)*rightStep) :
    2*(∫ z in (a:ℝ)..(b:ℝ), nearGap W d lo z) ≤
      (jointArea (rightSegment walls q) (foldedSegment walls lo i) d a b:ℝ) := by
  let r := rightSegment walls q
  let l := foldedSegment walls lo i
  have eq : (∫ z in (a:ℝ)..(b:ℝ), nearGap W d lo z) =
      (∫ z in (a:ℝ)..(b:ℝ), max 0 (value r z-value l z-d)) := by
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le (by exact_mod_cast hab)] at hz
    dsimp only [nearGap]
    rw [p.right_value q hq ⟨(by exact_mod_cast ra : (↑(q*rightStep):ℝ) ≤ a).trans hz.1,
      hz.2.trans (by exact_mod_cast rb)⟩, p.left_value lo i hi
      ⟨(by exact_mod_cast la : (↑(lo+i*leftStep):ℝ) ≤ a).trans hz.1,hz.2.trans (by exact_mod_cast lb)⟩]
  rw [eq]
  apply joint_integral_le _ _ _ _ _ _ _ hab
  · change ((q*rightStep:Nat):Int) < ((q+1)*rightStep:Nat)
    exact_mod_cast (by simp [Nat.add_mul] : q*rightStep < (q+1)*rightStep)
  · change ((lo+i*leftStep:Nat):Int) < (lo+(i+1)*leftStep:Nat)
    exact_mod_cast (by simp [Nat.add_mul] : lo+i*leftStep < lo+(i+1)*leftStep)

theorem row_bound {W : Wave.Datum} (p : Profile W) (d : Int) (lo i : Nat)
    (hi : i<17) :
    2*(∫ z in (↑(min height (lo+i*leftStep)):ℝ)..(↑(min height (lo+(i+1)*leftStep)):ℝ),
      nearGap W d lo z) ≤ (rowArea walls d lo i:ℝ) := by
  let a := min height (lo+i*leftStep)
  let b := min height (lo+(i+1)*leftStep)
  let q := a/rightStep
  let m := min b ((q+1)*rightStep)
  have hab : a≤b := min_le_min_left _ (by simp [Nat.add_mul])
  change 2*(∫ z in (a:ℝ)..(b:ℝ), nearGap W d lo z) ≤ _
  by_cases lt : a<b
  · have la : lo+i*leftStep≤a := by dsimp [a,b] at *; omega
    have lb : b≤lo+(i+1)*leftStep := min_le_right ..
    have qbounds : q*rightStep≤a ∧ a<(q+1)*rightStep := by
      dsimp [q,rightStep]; omega
    have bound : b≤500000000000 := min_le_left ..
    have qa : q*976562500≤a := qbounds.1
    have hq : q<512 := by omega
    have am : a≤m := le_min hab qbounds.2.le
    have mb : m≤b := min_le_left ..
    have first := cell_bound p d lo i q a m hi hq am la (mb.trans lb) qbounds.1 (min_le_right ..)
    have last : 2*(∫ z in (m:ℝ)..(b:ℝ), nearGap W d lo z) ≤
        (jointArea (rightSegment walls (q+1)) (foldedSegment walls lo i) d m b:ℝ) := by
      clear first
      by_cases e : m=b
      · rw [e]
        simp [jointArea]
      · have mEq : m=(q+1)*rightStep := min_eq_right (le_of_not_ge (fun h => e (min_eq_left h)))
        have mm : m=(q+1)*976562500 := mEq
        have qlt : q+1<512 := by omega
        apply cell_bound p d lo i (q+1) m b hi qlt mb (la.trans am) lb mEq.ge
        calc
          b ≤ lo+(i+1)*leftStep := lb
          _ = lo+i*leftStep+leftStep := by ring
          _ ≤ a+leftStep := Nat.add_le_add_right la _
          _ ≤ (q+1)*rightStep+rightStep := Nat.add_le_add qbounds.2.le (by decide)
          _ = (q+1+1)*rightStep := by simp only [Nat.add_mul,Nat.one_mul]
    have eq := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
      ((nearGap_cont W d lo).intervalIntegrable (a:ℝ) (m:ℝ))
      ((nearGap_cont W d lo).intervalIntegrable (m:ℝ) (b:ℝ))
    rw [←eq,mul_add]
    unfold rowArea
    rw [if_pos lt,Nat.cast_add]
    exact add_le_add first last
  · have eq := Nat.le_antisymm hab (Nat.le_of_not_gt lt)
    rw [eq]
    simp

end HadwigerNelson.Angular.Partial

import HadwigerNelson.Angular.Segments
import HadwigerNelson.Arithmetic.Positive

namespace HadwigerNelson.Angular
open Arithmetic MeasureTheory Set

/-- Clipping a segment in height and threshold gives the actual real area
enclosed by the leaf's integer evaluation. Ended segments contribute zero. -/
theorem Segment.integral_le (s : Segment) (hs : s.start < s.stop) (d lo : Int) :
    2*(∫ z in ((max s.start lo : Int):ℝ)..((max s.stop lo : Int):ℝ),
      max 0 (linearAt s.start s.left s.stop s.right z-d)) ≤ (s.area d lo : ℝ) := by
  by_cases after : s.stop ≤ lo
  · rw [max_eq_right (hs.le.trans after),max_eq_right after]
    simp [Segment.area,after]
  have before : lo < s.stop := lt_of_not_ge after
  rw [max_eq_left before.le]
  by_cases short : max s.left s.right ≤ d
  · obtain ⟨hl,hr⟩ := max_le_iff.mp short
    have hmax : max s.start lo ≤ s.stop := max_le hs.le before.le
    have eq : (∫ z in ((max s.start lo : Int):ℝ)..(s.stop:ℝ),
        max 0 (linearAt s.start s.left s.stop s.right z-d)) = 0 := by
      calc
        _ = ∫ _z in ((max s.start lo : Int):ℝ)..(s.stop:ℝ), (0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro z hz
          rw [Set.uIcc_of_le (by exact_mod_cast hmax)] at hz
          have left : (s.start:ℝ) ≤ z := (by exact_mod_cast le_max_left s.start lo : (s.start:ℝ) ≤ (max s.start lo:Int)).trans hz.1
          have he := linearAt_mono (by exact_mod_cast hs) left hz.2
            (by exact_mod_cast hl : (s.left:ℝ) ≤ d) (by exact_mod_cast hr : (s.right:ℝ) ≤ d)
          simp only [linearAt,sub_self,zero_mul,zero_div,add_zero] at he
          exact max_eq_left (sub_nonpos.mpr he)
        _ = 0 := by simp
    rw [eq]
    simp [Segment.area,short]
  by_cases initial : lo ≤ s.start
  · rw [max_eq_left initial]
    simp only [Segment.area,after,short,or_self,if_false,if_pos initial]
    have hh := integral_positive_linearAt_le s.start s.stop (s.left-d) (s.right-d) hs
    simpa only [Int.cast_sub,linearAt_sub] using hh
  · rw [max_eq_right (le_of_not_ge initial)]
    simp only [Segment.area,after,short,or_self,if_false,initial]
    exact integral_clipped_linearAt_le _ _ _ _ _ _ hs before

/-- Joining contiguous real intervals proves the correctness of the entire
compiled segment tree against the scaled profile. -/
theorem tabulate_integral_le (widths : Array Nat) (step : Nat) (hstep : 0 < step)
    (f : ℝ → ℝ) (hf : Continuous f) (d lo : Int) (depth first : Nat)
    (cells : ∀ q, first ≤ q → q < first+2^depth →
      ∀ z ∈ Set.Icc (↑(q*step):ℝ) (↑((q+1)*step):ℝ),
        f z = linearAt (↑(q*step):ℝ) (↑(widths[q]?.getD 0):ℝ)
           (↑((q+1)*step):ℝ) (↑(widths[q+1]?.getD 0):ℝ) z) :
    2*(∫ z in (max (↑(first*step):ℝ) (lo:ℝ))..(max (↑((first+2^depth)*step):ℝ) (lo:ℝ)),
      max 0 (f z-d)) ≤ ((tabulate widths step depth first).area d lo : ℝ) := by
  induction depth generalizing first with
  | zero =>
    let leaf : Segment := ⟨(↑first:Int)*step,((↑first:Int)+1)*step,
      widths[first]?.getD 0,widths[first+1]?.getD 0⟩
    have hstop : leaf.start < leaf.stop := (tabulate_valid widths step hstep 0 first)
    have eq := leaf.integral_le hstop d lo
    have ha : ((leaf.start:Int):ℝ) = ↑(first*step) := by simp [leaf]
    have hb : ((leaf.stop:Int):ℝ) = ↑((first+1)*step) := by simp [leaf]
    change _ ≤ (leaf.area d lo : ℝ)
    simp only [pow_zero,Int.cast_max,ha,hb] at eq ⊢
    by_cases h : (↑((first+1)*step):ℝ) ≤ lo
    · have le : (↑(first*step):ℝ) ≤ lo := by
        have lt : first*step ≤ (first+1)*step := Nat.mul_le_mul_right step (Nat.le_succ first)
        exact (by exact_mod_cast lt : (↑(first*step):ℝ) ≤ ↑((first+1)*step)).trans h
      simpa only [max_eq_right le,max_eq_right h,intervalIntegral.integral_same] using eq
    · have startLe : ↑(first*step) ≤ (↑((first+1)*step):ℝ) := by
        exact_mod_cast Nat.mul_le_mul_right step (Nat.le_succ first)
      have zz := le_of_not_ge h
      have upper : max (↑(first*step):ℝ) (lo:ℝ) ≤ ↑((first+1)*step) := max_le startLe zz
      rw [max_eq_left zz] at eq ⊢
      convert eq using 1
      congr 1
      apply intervalIntegral.integral_congr
      intro z hz
      rw [Set.uIcc_of_le upper] at hz
      have hz' := cells first le_rfl (by omega : first < first+2^0) z
        ⟨(le_max_left _ _).trans hz.1,hz.2⟩
      simp only [hz',leaf,Int.cast_natCast]
  | succ depth ih =>
    have endEq : first+2^(depth+1) = first+2^depth+2^depth := by rw [pow_succ]; omega
    let mid := first+2^depth
    have left := ih first (fun q h₁ h₂ => cells q h₁ (by omega))
    have right := ih mid (fun q h₁ h₂ => cells q (by dsimp [mid] at h₁; omega)
      (by dsimp [mid] at h₂; omega))
    have cont : Continuous fun z => max 0 (f z-d) := continuous_const.max (hf.sub continuous_const)
    have joined := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (cont.intervalIntegrable (max (↑(first*step):ℝ) (lo:ℝ)) (max (↑(mid*step):ℝ) (lo:ℝ)))
      (cont.intervalIntegrable (max (↑(mid*step):ℝ) (lo:ℝ)) (max (↑((mid+2^depth)*step):ℝ) (lo:ℝ)))
    rw [endEq,←joined]
    change _ ≤ (((tabulate widths step depth first).area d lo + (tabulate widths step depth mid).area d lo : Int):ℝ)
    rw [Int.cast_add,mul_add]
    exact add_le_add left right

end HadwigerNelson.Angular

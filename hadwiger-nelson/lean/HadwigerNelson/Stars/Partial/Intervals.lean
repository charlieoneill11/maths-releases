import HadwigerNelson.Stars.Partial.Wall

namespace HadwigerNelson.Stars.PartialCheck
open Set

noncomputable section

/-- On an interval a symmetric unimodal profile takes its minimum at one
of the endpoints, and its maximum at an endpoint or the middle. -/
private theorem arch_bounds (f : ℝ → ℝ)
    (rise : MonotoneOn f (Icc 0 250000000000))
    (flip : ∀ t, f (500000000000-t) = f t)
    {a b y : ℝ} (ha : 0 ≤ a) (hb : b ≤ 500000000000) (ay : a ≤ y) (yb : y ≤ b) :
    min (f a) (f b) ≤ f y ∧ f y ≤
      if a ≤ 250000000000 ∧ 250000000000 ≤ b then f 250000000000 else max (f a) (f b) := by
  have fall : AntitoneOn f (Icc 250000000000 500000000000) := by
    intro u hu v hv uv
    rw [←flip v,←flip u]
    exact rise ⟨by linarith [hv.2],by linarith [hv.1]⟩ ⟨by linarith [hu.2],by linarith [hu.1]⟩
      (by linarith)
  constructor
  · by_cases l : y ≤ 250000000000
    · exact (min_le_left ..).trans (rise ⟨ha,ay.trans l⟩ ⟨ha.trans ay,l⟩ ay)
    · exact (min_le_right ..).trans (fall ⟨le_of_not_ge l,yb.trans hb⟩ ⟨(le_of_not_ge l).trans yb,hb⟩ yb)
  · split
    · by_cases l : y ≤ 250000000000
      · exact rise ⟨ha.trans ay,l⟩ ⟨by norm_num,le_rfl⟩ l
      · exact fall ⟨le_rfl,by norm_num⟩ ⟨le_of_not_ge l,yb.trans hb⟩ (le_of_not_ge l)
    · rename_i no
      by_cases l : b ≤ 250000000000
      · exact (rise ⟨ha.trans ay,yb.trans l⟩ ⟨(ha.trans ay).trans yb,l⟩ yb).trans (le_max_right ..)
      · have a' : 250000000000 ≤ a := le_of_not_gt fun ha => no ⟨ha.le,le_of_not_ge l⟩
        exact (fall ⟨a',ay.trans (yb.trans hb)⟩ ⟨a'.trans ay,yb.trans hb⟩ ay).trans (le_max_left ..)

private theorem scaled_flip (f : ℝ → ℝ) (per : Function.Periodic f Wave.H)
    (even : ∀ y, f (-y) = f y) (y : ℝ) :
    scaled f (500000000000-y) = scaled f y := by
  unfold scaled
  rw [show (500000000000-y)/10^12 = Wave.H-y/10^12 by unfold Wave.H;ring,per.sub_eq',even]

private theorem scaled_increasing {f : ℝ → ℝ} (h : MonotoneOn f (Icc 0 (Wave.H/2))) :
    MonotoneOn (scaled f) (Icc 0 250000000000) := by
  intro a ha b hb ab
  have mem (v : ℝ) (hv : v∈Icc 0 (250000000000:ℝ)) : v/10^12∈Icc 0 (Wave.H/2) := by
    unfold Wave.H
    exact ⟨by linarith [hv.1],by linarith [hv.2]⟩
  exact mul_le_mul_of_nonneg_left (h (mem a ha) (mem b hb) (by linarith)) (by norm_num)

private theorem right_rises : MonotoneOn (scaled PartialWave.datum.right) (Icc 0 250000000000) := by
  apply scaled_increasing
  intro a ha b hb ab
  have half (t : ℝ) (ht : t ∈ Icc 0 (Wave.H/2)) : t ∈ Icc 0 Wave.H :=
    ⟨ht.1, by linarith [ht.2,Wave.H_pos]⟩
  rw [PartialWave.datum_right_on (half _ ha),PartialWave.datum_right_on (half _ hb)]
  exact PartialWave.rightAt_mono ha hb ab

private theorem neg_left_rises : MonotoneOn (fun y => -scaled PartialWave.datum.left y) (Icc 0 250000000000) := by
  have rise : MonotoneOn (fun y => -PartialWave.datum.left y) (Icc 0 (Wave.H/2)) :=
    fun _ ha _ hb ab => neg_le_neg (PartialWave.datum.left_antitone ha hb ab)
  intro a ha b hb ab
  have h := scaled_increasing rise ha hb ab
  simpa only [scaled,mul_neg] using h

/-- The four exact extrema used by a strip of the partial-wave classifier. -/
theorem wall_bounds (a b : Int) (y : ℝ) (ha : 0 ≤ a) (hb : b ≤ 500000000000)
    (ay : a ≤ y) (yb : y ≤ b) :
    let mid := a ≤ 250000000000 && 250000000000 ≤ b
    ((if mid then 0 else min (left a).1 (left b).1 : Int):ℝ) ≤ scaled PartialWave.datum.left y ∧
    scaled PartialWave.datum.left y ≤ ((max (left a).2 (left b).2 : Int):ℝ) ∧
    ((min (right a).1 (right b).1 : Int):ℝ) ≤ scaled PartialWave.datum.right y ∧
    scaled PartialWave.datum.right y ≤ ((if mid then peak else max (right a).2 (right b).2 : Int):ℝ) := by
  have hab : a ≤ b := by exact_mod_cast ay.trans yb
  have ar : (0:ℝ) ≤ a := by exact_mod_cast ha
  have br : (b:ℝ) ≤ 500000000000 := by exact_mod_cast hb
  have ⟨la,ua⟩ := left_integer a ha (hab.trans hb)
  have ⟨lb,ub⟩ := left_integer b (ha.trans hab) hb
  have ⟨ra,va⟩ := right_integer a ha (hab.trans hb)
  have ⟨rb,vb⟩ := right_integer b (ha.trans hab) hb
  have ⟨minR,maxR⟩ := arch_bounds _ right_rises
    (scaled_flip _ PartialWave.datum.right_periodic PartialWave.datum.right_even) ar br ay yb
  have ⟨minL,maxL⟩ := arch_bounds _ neg_left_rises (fun t =>
    congrArg Neg.neg (scaled_flip _ PartialWave.datum.left_periodic PartialWave.datum.left_even t)) ar br ay yb
  dsimp only at minL maxL ⊢
  rw [min_neg_neg] at minL
  have upperL := neg_le_neg_iff.mp minL
  have lowerR := (min_le_min ra rb).trans minR
  have upperL' := upperL.trans (max_le_max ua ub)
  rw [Int.cast_max,Int.cast_min]
  refine ⟨?_,upperL',lowerR,?_⟩
  all_goals simp only [Bool.and_eq_true, decide_eq_true_eq]
  all_goals by_cases mid : a ≤ 250000000000 ∧ 250000000000 ≤ b
  · rw [if_pos mid,Int.cast_zero]
    exact mul_nonneg (by norm_num : 0 ≤ (10:ℝ)^12) (PartialWave.datum.left_bounds _).1
  · have m : ¬((a:ℝ) ≤ 250000000000 ∧ 250000000000 ≤ (b:ℝ)) := by exact_mod_cast mid
    rw [if_neg mid,Int.cast_min]
    rw [if_neg m,max_neg_neg] at maxL
    exact (min_le_min la lb).trans (neg_le_neg_iff.mp maxL)
  · have m : (a:ℝ) ≤ 250000000000 ∧ 250000000000 ≤ (b:ℝ) := by exact_mod_cast mid
    rw [if_pos mid]
    rw [if_pos m] at maxR
    exact maxR.trans ((right_integer 250000000000 (by decide) (by decide)).2)
  · have m : ¬((a:ℝ) ≤ 250000000000 ∧ 250000000000 ≤ (b:ℝ)) := by exact_mod_cast mid
    rw [if_neg mid,Int.cast_max]
    rw [if_neg m] at maxR
    exact maxR.trans (max_le_max va vb)

end
end HadwigerNelson.Stars.PartialCheck

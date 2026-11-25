import HadwigerNelson.Wave.Geometry.PartialLeft
import HadwigerNelson.Wave.Geometry.Interval
import HadwigerNelson.Wave.Geometry.PeriodicLipschitz

namespace HadwigerNelson.PartialWave
open Wave Angular.Grid
noncomputable section

private theorem exists_datum : ∃ W : Datum, W.x=(xq:ℝ) ∧ W.y0=cutoff ∧
    Set.EqOn W.left leftAt (Set.Icc 0 H) ∧ Set.EqOn W.right rightAt (Set.Icc 0 H) :=
  partial_of_interval xq cutoff leftAt rightAt (by norm_num [xq]) (by norm_num [cutoff,H])
    leftAt_rational rightAt_rational leftAt_continuous.continuousOn rightAt_continuous.continuousOn
    (fun y _ => leftAt_reflect y) rightAt_reflect rightAt_complement leftAt_bounds rightAt_bounds
    leftAt_antitone leftAt_zero

/-- The partial wave W_V in the release. Its two continuous periodic profiles agree
with the literal rational polygonal profiles on the whole closed tile interval. -/
def datum : Datum := Classical.choose exists_datum

theorem datum_x : datum.x=923111560246/10^12 := by
  have h := (Classical.choose_spec exists_datum).1
  norm_num [datum,xq] at h ⊢
  exact h

theorem datum_y0 : datum.y0=918/100000 := by
  have h := (Classical.choose_spec exists_datum).2.1
  norm_num [datum,cutoff] at h ⊢
  exact h

theorem datum_left_on : Set.EqOn datum.left leftAt (Set.Icc 0 H) := (Classical.choose_spec exists_datum).2.2.1

theorem datum_right_on : Set.EqOn datum.right rightAt (Set.Icc 0 H) := (Classical.choose_spec exists_datum).2.2.2

theorem datum_right_lipschitz {s t : ℝ} (hs : s∈Set.Icc 0 H) (ht : t∈Set.Icc 0 H) :
    |datum.right s-datum.right t| ≤ |s-t| := by
  rw [datum_right_on hs,datum_right_on ht]; exact rightAt_lipschitz s t hs ht

theorem datum_left_lipschitz {s t : ℝ} (hs : s∈Set.Icc 0 H) (ht : t∈Set.Icc 0 H) :
    |datum.left s-datum.left t| ≤ |s-t| := by
  rw [datum_left_on hs,datum_left_on ht]; exact leftAt_lipschitz s t hs ht

theorem datum_right_lipschitz_all (s t : ℝ) : |datum.right s-datum.right t| ≤ |s-t| :=
  periodic_lipschitz datum.right_periodic (fun _ hs _ ht => datum_right_lipschitz hs ht) s t

theorem datum_left_lipschitz_all (s t : ℝ) : |datum.left s-datum.left t| ≤ |s-t| :=
  periodic_lipschitz datum.left_periodic (fun _ hs _ ht => datum_left_lipschitz hs ht) s t

theorem datum_right_mono : MonotoneOn datum.right (Set.Icc 0 (H/2)) := by
  have sub : Set.Icc 0 (H/2) ⊆ Set.Icc 0 H := fun _ hz => ⟨hz.1,by linarith [hz.2,H_pos]⟩
  intro s hs t ht le
  rw [datum_right_on (sub hs),datum_right_on (sub ht)]
  exact rightAt_mono hs ht le

private theorem left_bang (i : Nat) (hi : i<37) : leftKnots[i]! = leftKnot i := by
  rw [getElem!_pos _ _ (by simpa [leftKnots] using hi),get_leftKnots _ hi]

private theorem right_bang (i : Nat) (hi : i<513) : rightKnots[i]! = rightKnot i := by
  rw [getElem!_pos _ _ (by simpa [rightKnots] using hi),get_rightKnots _ hi]

/-- Barycentric formula on every active left segment, in physical coordinates. -/
theorem datum_left_segment (i : Fin 17) (u : ℝ) (hu : u ∈ Set.Icc 0 1) :
    datum.left (((i:ℝ)+u)*54/100000) =
    ((1-u)*(leftKnots[i.val]!.2:ℝ)+u*(leftKnots[i.val+1]!.2:ℝ))/10^12 := by
  have il : 0 ≤ (i:ℝ) := by positivity
  have iu : (i:ℝ) ≤ 16 := by exact_mod_cast (show i.val ≤ 16 by omega)
  let y := ((i:ℝ)+u)*54/100000
  have lo := hu.1; have up := hu.2
  have hy : y∈Set.Icc 0 H := by dsimp [y,H]; constructor <;> linarith
  have a : (leftStep:ℝ)=54/100000 := by norm_num [leftStep]
  have hy' : leftArg y=(i:ℝ)+u := by
    unfold leftArg
    rw [min_eq_left (show y≤H-y by dsimp [y,H]; linarith),a,
      show y/(54/100000)=(i:ℝ)+u by dsimp [y]; ring,min_eq_right (by linarith)]
  change datum.left y = _
  rw [datum_left_on hy,leftAt,hy',interpolation_on _ i.isLt ⟨by linarith,by linarith⟩,
    left_bang _ (by omega),left_bang _ (by omega)]
  simp only [leftOrd,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat]
  ring

/-- Barycentric formula on all 512 segments of the right side. -/
theorem datum_right_segment (i : Fin 512) (u : ℝ) (hu : u ∈ Set.Icc 0 1) :
    datum.right (((i:ℝ)+u)*H/512) =
    ((1-u)*(rightKnots[i.val]!.2:ℝ)+u*(rightKnots[i.val+1]!.2:ℝ))/10^12 := by
  have il : 0 ≤ (i:ℝ) := by positivity
  have iu : (i:ℝ) ≤ 511 := by exact_mod_cast (show i.val ≤ 511 by omega)
  let y := ((i:ℝ)+u)*H/512
  have lo := hu.1; have up := hu.2
  have hy : y∈Set.Icc 0 H := by dsimp [y,H]; constructor <;> linarith
  change datum.right y = _
  rw [datum_right_on hy,rightAt,show 1024*y=(i:ℝ)+u by dsimp [y,H]; ring,
    interpolation_on _ i.isLt ⟨by linarith,by linarith⟩,right_bang _ (by omega),right_bang _ (by omega)]
  simp only [rightOrd,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat]
  ring

/-- Each height in the literal left table samples the published ordinate,
including both rows flanking the flat portion and the middle knot. -/
theorem datum_left_knot (i : Nat) (hi : i≤36) :
    datum.left ((leftKnot i).1/1000000000000) = (leftKnot i).2/1000000000000 := by
  have lower (j : Nat) (hj : j ≤ 17) :
      datum.left ((leftKnot j).1/1000000000000) = (leftKnot j).2/1000000000000 := by
    by_cases edge : j=17
    · subst j
      have a := datum_left_segment ⟨16,by decide⟩ 1 ⟨by norm_num,le_rfl⟩
      have h : (leftKnot 17).1=9180000000 := by decide +kernel
      norm_num [left_bang _ (show 17<37 by decide)] at a
      rw [h]; convert a using 1 <;> norm_num
    have jj : j<17 := by omega
    have a := datum_left_segment ⟨j,jj⟩ 0 ⟨le_rfl,by norm_num⟩
    rw [left_bang j (by omega)] at a
    have step := (left_knot_ok j (by omega)).2.2.1.1 hj
    rw [step,Nat.cast_mul]; norm_num at a ⊢; convert a using 1 <;> ring
  by_cases low : i≤17
  · exact lower i low
  by_cases mid : i=18
  · subst i
    have knot : leftKnot 18 = (250000000000,0) := by decide +kernel
    rw [knot]
    have a := datum.left_zero (H/2) ⟨by rw [datum_y0]; norm_num [H],le_rfl⟩
    convert a using 1 <;> norm_num [H]
  let j := 36-i
  have hj : j≤17 := by dsimp [j]; omega
  have r := lower j hj
  have h := left_knot_ok i hi
  have heights : ((leftKnot i).1:ℝ)+(leftKnot j).1=500000000000 := by exact_mod_cast h.1
  have e : ((leftKnot i).1:ℝ)/1000000000000 = H-(leftKnot j).1/1000000000000 := by unfold H; linarith
  rw [e,datum.left_periodic.sub_eq',datum.left_even,r,h.2.1]

/-- Every literal right knot lies on the fixed real profile. -/
theorem datum_right_knot (i : Nat) (hi : i≤512) :
    datum.right ((rightKnot i).1/1000000000000) = (rightKnot i).2/1000000000000 := by
  by_cases edge : i=512
  · subst i
    have a := datum_right_segment ⟨511,by decide⟩ 1 ⟨by norm_num,le_rfl⟩
    have h : (rightKnot 512).1=500000000000 := by decide +kernel
    norm_num [right_bang _ (show 512<513 by decide),H] at a
    rw [h]; convert a using 1 <;> norm_num
  have ii : i<512 := by omega
  have a := datum_right_segment ⟨i,ii⟩ 0 ⟨le_rfl,by norm_num⟩
  rw [right_bang i (by omega)] at a
  rw [(right_knot_ok i hi).2.2.1.1,Nat.cast_mul]; norm_num [H] at a ⊢; convert a using 1 <;> ring

end
end HadwigerNelson.PartialWave

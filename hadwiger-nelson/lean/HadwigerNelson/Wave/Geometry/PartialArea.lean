import HadwigerNelson.Wave.Geometry.Partial
import HadwigerNelson.Wave.Geometry.ProfileIntegral

namespace HadwigerNelson.PartialWave
open Wave MeasureTheory Set
noncomputable section

private def height (i : Nat) : ℝ := (i:ℝ)*54/100000
private def val (i : Nat) : Nat := (leftKnot i).2

private theorem value_at (i : Nat) (hi : i<37) : leftKnots[i]!.2 = val i := by
  rw [getElem!_pos _ _ (by simpa [leftKnots] using hi),get_leftKnots _ hi]
  rfl

private theorem ordinate_sum : ∑ i ∈ Finset.range 17, (val i + val (i+1)) = 60816642020 := by
  decide +kernel

private theorem integral_symmetric_segment (f : ℝ → ℝ) (cont : Continuous f) (a b k : ℝ) (ab : a≤b)
    (h : ∀ x ∈ Icc a b, f x+f (a+b-x)=k) :
    (∫ x in a..b, f x) = (b-a)*k/2 := by
  have anti := intervalIntegral.integral_comp_sub_left (a:=a) (b:=b) f (a+b)
  rw [show a+b-b=a by ring,show a+b-a=b by ring] at anti
  have both := intervalIntegral.integral_add (cont.intervalIntegrable a b)
    ((cont.comp (continuous_const.sub continuous_id)).intervalIntegrable a b :
      IntervalIntegrable (fun x => f (a+b-x)) volume a b)
  have const : (∫ x in a..b, f x+f (a+b-x)) = ∫ _ in a..b, k := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact h x (by simpa only [uIcc_of_le ab] using hx)
  simp only [Function.comp_apply,id_eq] at both
  rw [both,anti,intervalIntegral.integral_const,smul_eq_mul] at const
  linarith

private theorem mirror_on_segment (W : Datum)
    (segments : ∀ i : Fin 17, ∀ u ∈ Icc (0:ℝ) 1, W.left (((i:ℝ)+u)*54/100000) =
      ((1-u)*(leftKnots[i.val]!.2:ℝ)+u*(leftKnots[i.val+1]!.2:ℝ))/10^12)
    (i : Nat) (hi : i<17) (y : ℝ) (hy : y∈Icc (height i) (height (i+1))) :
    W.left y+W.left (height i+height (i+1)-y) = ((val i+val (i+1):Nat):ℝ)/10^12 := by
  let u := (y-height i)/(54/100000)
  have h0 := hy.1; have h1 := hy.2
  unfold height at h0 h1
  push_cast at h1
  have hu : u∈Icc 0 1 := by dsimp [u,height]; constructor <;> linarith
  have a := segments ⟨i,hi⟩ u hu
  have b := segments ⟨i,hi⟩ (1-u) ⟨by linarith [hu.2],by linarith [hu.1]⟩
  change W.left (((i:ℝ)+u)*54/100000)=_ at a
  change W.left (((i:ℝ)+(1-u))*54/100000)=_ at b
  have e : ((i:ℝ)+u)*54/100000=y := by dsimp [u,height]; ring
  have e' : ((i:ℝ)+(1-u))*54/100000=height i+height (i+1)-y := by dsimp [u,height]; push_cast; ring
  rw [e] at a
  rw [e'] at b
  rw [a,b]
  change ((1-u)*(leftKnots[i]!.2:ℝ)+u*(leftKnots[i+1]!.2:ℝ))/10^12 +
    ((1-(1-u))*(leftKnots[i]!.2:ℝ)+(1-u)*(leftKnots[i+1]!.2:ℝ))/10^12 = _
  rw [value_at _ (by omega),value_at _ (by omega),Nat.cast_add]; ring

/-- The exact area under one periodic left profile from its sixteen interior
knots and its closing zero knot. Above the cutoff it vanishes on the lower
half, and the upper half is its reflection. -/
theorem integral_left_of_segments (W : Datum) (hy0 : W.y0 = 918/100000)
    (segments : ∀ i : Fin 17, ∀ u ∈ Icc (0:ℝ) 1, W.left (((i:ℝ)+u)*54/100000) =
      ((1-u)*(leftKnots[i.val]!.2:ℝ)+u*(leftKnots[i.val+1]!.2:ℝ))/10^12) :
    (∫ y in 0..H, W.left y) = 82102466727 / 2500000000000000 := by
  have hi (a b : ℝ) := W.left_continuous.intervalIntegrable (μ:=volume) a b
  have seg (i : Nat) (ii : i<17) : (∫ y in height i..height (i+1), W.left y) =
      (54/100000/10^12/2:ℝ) * ((val i+val (i+1):Nat):ℝ) := by
    have gap : height (i+1)-height i=54/100000 := by dsimp [height]; push_cast; ring
    rw [integral_symmetric_segment W.left W.left_continuous _ _ _ (by linarith) (mirror_on_segment W segments i ii),gap]
    ring
  have sum := intervalIntegral.sum_integral_adjacent_intervals (n:=17) (a:=height) (f:=W.left) (fun _ _ => hi _ _)
  have replace := Finset.sum_congr rfl (fun i (ii : i∈Finset.range 17) => seg i (Finset.mem_range.mp ii))
  rw [replace,← Finset.mul_sum,← Nat.cast_sum,ordinate_sum] at sum
  have start : height 0=0 := by norm_num [height]
  have stop : height 17=W.y0 := by rw [hy0]; norm_num [height]
  rw [start,stop] at sum
  rw [Wave.integral_left_support W]
  linarith


theorem integral_left : (∫ y in 0..H, datum.left y) = 82102466727 / 2500000000000000 :=
  integral_left_of_segments datum datum_y0 datum_left_segment

end
end HadwigerNelson.PartialWave

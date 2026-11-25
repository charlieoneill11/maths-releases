import HadwigerNelson.Stars.ArcAnalytic
import HadwigerNelson.Stars.FullTurn
import HadwigerNelson.Stars.MomentSums

/-! Prefix primitives for the integer mean, radius, and certainly-native spans. -/

namespace HadwigerNelson.Stars.BoxCheck

noncomputable def arcLowAt (i : Nat) : ℝ := ((arcTable[i]?.getD default).low : ℝ)
noncomputable def arcHighAt (i : Nat) : ℝ := ((arcTable[i]?.getD default).high : ℝ)

noncomputable def meanWeight (_ : Nat) (c r : Int) (i : Nat) : ℝ :=
  (c-r : Int)*(if c-r < 0 then arcHighAt i else arcLowAt i)
noncomputable def errorWeight (_ : Nat) (_ r : Int) (i : Nat) : ℝ :=
  r*arcHighAt i/phaseScale
noncomputable def nativeWeight (_ : Nat) (c r : Int) (i : Nat) : ℝ :=
  if c == 2 && r == 0 then arcLowAt i else 0

theorem meanWeight_ticks (s : Array Span) :
    (spanSum (s.map (prepareSpan arcTable)) SpanMoments.mean : ℝ) = spanEval s (changeOf meanWeight) := by
  rw [spanSum_eq,spanEval_cast]
  congr 1
  funext p
  simp only [prepareSpan,changeOf,meanWeight]
  split <;> simp_all [spanArc,arcLowAt,arcHighAt,mul_sub]

theorem errorWeight_ticks (s : Array Span) :
    (spanSum (s.map (prepareSpan arcTable)) SpanMoments.error : ℝ)/phaseScale =
      spanEval s (changeOf errorWeight) := by
  rw [spanSum_eq,spanEval_cast,spanEval_fin,spanEval_fin,div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp [spanArc,arcHighAt,prepareSpan,changeOf,errorWeight,div_eq_mul_inv]
  ring

theorem nativeWeight_ticks (s : Array Span) :
    (nativeTicks arcTable s : ℝ) = spanEval s (changeOf nativeWeight) := by
  rw [nativeTicks,array_sum_by,Int.cast_sum,spanEval_fin]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : s[i.val].coeff == 2 && s[i.val].radius == 0
  · simp [h,changeOf,nativeWeight,spanArc,arcLowAt]
  · simp [h,changeOf,nativeWeight]

theorem arc_low_high (q a b : Nat) (hab : a ≤ b) (hb : b ≤ resolution) :
    arcLowAt b-arcLowAt a ≤ phaseScale*(endpoint q b-endpoint q a) ∧
    phaseScale*(endpoint q b-endpoint q a) ≤ arcHighAt b-arcHighAt a := by
  let p : Span := ⟨q,a,b,0,0⟩
  have ⟨lo,hi⟩ := actual_spanArc_bounds p hab hb
  have id : (phaseScale : ℝ)*(endpoint q b-endpoint q a) = phaseAngle b-phaseAngle a := by
    unfold endpoint paramAngle phaseAngle; ring
  rw [id]
  simpa [p,spanArc,arcLowAt,arcHighAt] using And.intro lo hi

theorem meanWeight_bound (p : Span) (hab : p.start ≤ p.stop) (hb : p.stop ≤ resolution) :
    changeOf meanWeight p ≤
      phaseScale*((p.coeff : ℝ)-p.radius)*(endpoint p.quadrant p.stop-endpoint p.quadrant p.start) := by
  obtain ⟨lo,hi⟩ := arc_low_high p.quadrant p.start p.stop hab hb
  unfold changeOf meanWeight
  by_cases signed : p.coeff-p.radius < 0
  · simp only [signed,if_true,Int.cast_sub]
    have sign : (p.coeff : ℝ)-p.radius ≤ 0 := by exact_mod_cast signed.le
    linarith only [mul_le_mul_of_nonpos_left hi sign]
  · simp only [signed,if_false,Int.cast_sub]
    have sign : (0 : ℝ) ≤ p.coeff-p.radius := by exact_mod_cast le_of_not_gt signed
    linarith only [mul_le_mul_of_nonneg_left lo sign]

theorem errorWeight_bound (p : Span) (hab : p.start ≤ p.stop) (hb : p.stop ≤ resolution)
    (hr : 0 ≤ p.radius) :
    (p.radius : ℝ)*(endpoint p.quadrant p.stop-endpoint p.quadrant p.start) ≤ changeOf errorWeight p := by
  have hi := (arc_low_high p.quadrant p.start p.stop hab hb).2
  have s : (0 : ℝ) < phaseScale := by norm_num [phaseScale]
  have h := mul_le_mul_of_nonneg_left hi (show (0 : ℝ) ≤ p.radius by exact_mod_cast hr)
  unfold changeOf errorWeight
  rw [←sub_div]
  apply (le_div_iff₀ s).2
  linarith only [h]

theorem radius_nonneg (s : Angular.Box) (other q a b : Nat) :
    0 ≤ (nodeSpan s other q a b).radius := by
  change 0 ≤ (signedStep _ _).2
  generalize classify _ 1 = n
  generalize classify _ other = m
  cases n <;> cases m <;> decide

end HadwigerNelson.Stars.BoxCheck

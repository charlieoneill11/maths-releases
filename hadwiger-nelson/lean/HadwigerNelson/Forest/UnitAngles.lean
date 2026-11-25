import HadwigerNelson.Forest.BlankPairs
import HadwigerNelson.Placement.UnitDirection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.MeasureTheory.Function.Floor

/-! Write each oriented unit displacement as an angular translate of the
same even vertical window. Its exact mean is the sum of the cell masses. -/

namespace HadwigerNelson.Forest
open MeasureTheory Set Placement Centres Wave
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def circularDistance (t : ℝ) := Real.arccos (Real.cos t)

theorem circularDistance_abs {t : ℝ} (ht : |t|≤Real.pi) : circularDistance t=|t| := by
  unfold circularDistance
  rw [← Real.cos_abs t,Real.arccos_cos (abs_nonneg _) ht]

theorem circularDistance_principal (t : ℝ) : circularDistance t = |(t : Real.Angle).toReal| := by
  have c : Real.cos ((t : Real.Angle).toReal)=Real.cos t := Real.Angle.cos_toReal _
  rw [circularDistance,← c,← Real.cos_abs,Real.arccos_cos (abs_nonneg _) (Real.Angle.abs_toReal_le_pi _)]

def verticalCell (t : ℝ) : ℕ := min 16384 (max 1 ⌈t/unitBin 1⌉₊)

def verticalWindow (f : ℕ → ℝ) (s : ℝ) : ℝ :=
  if circularDistance s ≤ w then f (verticalCell (circularDistance s)) else 0

theorem verticalWindow_period (f : ℕ → ℝ) : Function.Periodic (verticalWindow f) (2*Real.pi) :=
  fun θ => by simp [verticalWindow,circularDistance]

theorem verticalWindow_int (f : ℕ → ℝ) (a b : ℝ) : IntervalIntegrable (verticalWindow f) volume a b := by
  have meas : Measurable (verticalWindow f) := by
    have dist : Measurable circularDistance := Real.continuous_arccos.measurable.comp Real.continuous_cos.measurable
    have cellm : Measurable verticalCell := by unfold verticalCell; fun_prop
    exact Measurable.ite (measurableSet_le dist measurable_const) ((measurable_of_countable f).comp (cellm.comp dist)) measurable_const
  apply intervalIntegrable_iff.mpr
  apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne meas.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro s
  unfold verticalWindow
  split
  · exact Finset.single_le_sum (f:=fun i => ‖f i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.mpr ((min_le_left _ _).trans_lt (by decide : 16384<16385)))
  · simp only [norm_zero]; exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem verticalWindow_integrable_uniform (f : ℕ → ℝ) (φ : ℝ) :
    Integrable (fun θ => verticalWindow f (θ+φ)) (uniformInterval (2*Real.pi)) := by
  have hi := (verticalWindow_int f (0+φ) (2*Real.pi+φ)).comp_add_right φ
  have h : IntervalIntegrable (fun θ => verticalWindow f (θ+φ)) volume 0 (2*Real.pi) := by
    simpa only [add_sub_cancel_right] using hi
  exact h.1.smul_measure (by
    change (ENNReal.ofReal (2*Real.pi))⁻¹ ≠ ⊤
    rw [ENNReal.inv_ne_top,ENNReal.ofReal_ne_zero_iff]
    positivity)

theorem unitCandidate_unit {θ : ℝ} {x y : Plane} (h : unitCandidate θ x y) : dist x y=1 := by
  obtain ⟨t,_,e⟩ := h
  apply (sq_eq_sq₀ dist_nonneg zero_le_one).mp
  rw [dist_comm,← rotate_dist θ,dist_eq_norm,← rotate_sub,e,← dist_zero_right,coord_dist_sq]
  simpa using Real.sin_sq_add_cos_sq t

theorem unit_phase {x y : Plane} (hxy : dist x y=1) : ∃ φ : ℝ, ∀ θ,
    rotate θ (y-x)=point (-Real.sin (θ+φ)) (Real.cos (θ+φ)) := by
  obtain ⟨α,ha⟩ := rotated_unit_displacement hxy
  refine ⟨α-Real.pi/2,fun θ => ?_⟩
  rw [rotate_sub,ha,show θ+(α-Real.pi/2)=θ+α-Real.pi/2 by ring,Real.sin_sub_pi_div_two,Real.cos_sub_pi_div_two,neg_neg]

private theorem witness_iff (s : ℝ) :
    (∃ t, |t|≤w ∧ point (-Real.sin s) (Real.cos s)=point (Real.sin t) (Real.cos t)) ↔ circularDistance s≤w := by
  constructor
  · rintro ⟨t,ht,e⟩
    have c := congrArg (fun v : Plane => v 1) e
    change Real.cos s=Real.cos t at c
    rw [circularDistance,c,← Real.cos_abs t,Real.arccos_cos (abs_nonneg _) (by linarith [ht,Real.two_le_pi,show w≤1 by norm_num [w]])]
    exact ht
  · intro h
    let t := (s : Real.Angle).toReal
    refine ⟨-t,by simpa only [t,abs_neg,← circularDistance_principal] using h,?_⟩
    have si : Real.sin t=Real.sin s := Real.Angle.sin_toReal _
    have co : Real.cos t=Real.cos s := Real.Angle.cos_toReal _
    rw [Real.sin_neg,Real.cos_neg,si,co]

theorem edgeUnit_phase (Ω : ℝ → ℝ → ℝ) {φ θ : ℝ} {x y : Plane}
    (disp : rotate θ (y-x)=point (-Real.sin (θ+φ)) (Real.cos (θ+φ))) :
    edgeUnit Ω θ x y=verticalWindow (unitStep Ω) (θ+φ) := by
  let s := θ+φ
  have c : unitCandidate θ x y ↔ circularDistance s≤w := by
    unfold unitCandidate
    rw [disp]
    exact witness_iff s
  by_cases yes : unitCandidate θ x y
  · obtain ⟨t,ht,he⟩ := yes
    have hh : unitCandidate θ x y := ⟨_,ht,he⟩
    have recover : Real.arcsin (Real.sin t)=t := Real.arcsin_sin
      (by linarith [(abs_le.mp ht).1,Real.two_le_pi,show w≤1 by norm_num [w]])
      (by linarith [(abs_le.mp ht).2,Real.two_le_pi,show w≤1 by norm_num [w]])
    have cosine := congrArg (fun z : Plane => z 1) (disp.symm.trans he)
    change Real.cos s=Real.cos t at cosine
    have dis : circularDistance s=|t| := by unfold circularDistance; rw [cosine,← Real.cos_abs,
      Real.arccos_cos (abs_nonneg _) (by linarith [ht,Real.two_le_pi,show w≤1 by norm_num [w]])]
    change edgeUnit Ω θ x y=verticalWindow (unitStep Ω) s
    simp only [edgeUnit,if_pos hh,he,point_fst,recover,verticalWindow,dis,if_pos ht,verticalCell,unitCredit]
  · change edgeUnit Ω θ x y=verticalWindow (unitStep Ω) s
    simp only [edgeUnit,if_neg yes,verticalWindow,if_neg (c.not.mp yes)]

private theorem in_cell {i : ℕ} (hi : i < 16384) {u : ℝ} (h : u∈Ioc (unitBin i) (unitBin (i+1))) :
   verticalCell u=i+1 := by
  have step : 0<unitBin 1 := by norm_num [unitBin,w]
  have formula (j : ℕ) : unitBin j=(j:ℝ)*unitBin 1 := by unfold unitBin; simp [mul_div_assoc]
  obtain ⟨lo,up⟩ := h
  rw [formula] at lo up
  have z : ⌈u/unitBin 1⌉₊=i+1 := (Nat.ceil_eq_iff (by omega)).mpr ⟨by
    simp only [Nat.add_sub_cancel]; exact (lt_div_iff₀ step).mpr lo,(div_le_iff₀ step).mpr up⟩
  simp only [verticalCell,z,max_eq_right (by omega : 1 ≤ i + 1),min_eq_right (by omega : i+1≤16384)]

theorem verticalWindow_average (f : ℕ → ℝ) (φ : ℝ) :
    (∫ θ,verticalWindow f (θ+φ) ∂uniformInterval (2*Real.pi)) =
      unitBin 1/Real.pi * ∑ k : Fin 16384,f (k.val+1) := by
  let g := verticalWindow f
  have even (t : ℝ) : g (-t)=g t := by simp [g,verticalWindow,circularDistance]
  have hw : (0:ℝ)≤w ∧ w≤Real.pi := ⟨by norm_num [w],by linarith [Real.two_le_pi,show w≤1 by norm_num [w]]⟩
  have stay (i : ℕ) (hi : i≤16384) : unitBin i≤w := by
    have r : (i:ℝ)≤16384 := by exact_mod_cast hi
    unfold unitBin w
    linarith only [r]
  have endpts : unitBin 0=0 ∧ unitBin 16384=w := ⟨by simp [unitBin],by norm_num [unitBin,w]⟩
  have each (i : ℕ) (hi : i<16384) :
      (∫ t in unitBin i..unitBin (i+1),g t)=unitBin 1*f (i+1) := by
    have order : unitBin i≤unitBin (i+1) := by simp only [unitBin,w,Nat.cast_add,Nat.cast_one]; linarith
    calc _ = ∫ _ in unitBin i..unitBin (i+1),f (i+1) := by
           apply intervalIntegral.integral_congr_ae
           apply Filter.Eventually.of_forall
           intro t ht
           rw [uIoc_of_le order] at ht
           have pos : 0≤t := (show 0≤unitBin i by unfold unitBin w; positivity).trans ht.1.le
           have core := ht.2.trans (stay _ (by omega))
           dsimp [g, verticalWindow]
           rw [circularDistance_abs (by rw [abs_of_nonneg pos]; exact core.trans hw.2),abs_of_nonneg pos,if_pos core,in_cell hi ht]
         _ = _ := by simp only [intervalIntegral.integral_const,smul_eq_mul]; congr 1; simp [unitBin]; ring
  have inside : (∫ t in 0..w,g t)=unitBin 1*∑ k:Fin 16384,f (k.val+1) := by
    have sum := intervalIntegral.sum_integral_adjacent_intervals (a:=unitBin) (n:=16384)
      (fun i _ => verticalWindow_int f (unitBin i) (unitBin (i+1)))
    rw [endpts.1,endpts.2] at sum
    rw [← sum,Finset.mul_sum,Fin.sum_univ_eq_sum_range (fun i => unitBin 1*f (i+1))]
    exact Finset.sum_congr rfl (fun i hi => each i (Finset.mem_range.mp hi))
  have outside : ∫ t in w..Real.pi,g t=0 := by
    apply intervalIntegral.integral_zero_ae
    apply Filter.Eventually.of_forall
    intro t ht
    rw [uIoc_of_le hw.2] at ht
    have pos := hw.1.trans ht.1.le
    simp [g,verticalWindow,circularDistance_abs (t:=t) (by simpa [abs_of_nonneg pos] using ht.2),abs_of_nonneg pos,not_le_of_gt ht.1]
  have right := intervalIntegral.integral_add_adjacent_intervals (verticalWindow_int f 0 w) (verticalWindow_int f w Real.pi)
  rw [outside,add_zero] at right
  have flip := intervalIntegral.integral_comp_neg (a:=0) (b:=Real.pi) g
  simp only [even,neg_zero] at flip
  have whole := intervalIntegral.integral_add_adjacent_intervals
    (verticalWindow_int f (-Real.pi) 0) (verticalWindow_int f 0 Real.pi)
  have shift := (verticalWindow_period f).intervalIntegral_add_eq φ (-Real.pi)
  rw [integral_uniformInterval (by linarith [Real.pi_pos]),intervalIntegral.integral_comp_add_right]
  rw [zero_add,add_comm (2*Real.pi) φ,shift,show -Real.pi+2*Real.pi=Real.pi by ring]
  change (2*Real.pi)⁻¹ * (∫ t in -Real.pi..Real.pi,g t)=_
  rw [← whole,← flip,← right,inside]
  ring

end
end HadwigerNelson.Forest

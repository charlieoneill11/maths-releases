import HadwigerNelson.Centres.Events.Measurable
import HadwigerNelson.Placement.Law
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Average conditional translation probabilities over the two signed angular
sectors in Lemma 49. The sectors can have arbitrary phase and cover only a
portion of each half-turn. -/

namespace HadwigerNelson.Centres.Events
noncomputable section
open Set MeasureTheory Placement
open scoped BigOperators

theorem sector_probability_lower (W : Wave.Datum) (E : Set Sample) (meas : MeasurableSet E)
    (per : Function.Periodic (fun θ => (translationLaw W).real (Prod.mk θ ⁻¹' E)) (2*Real.pi))
    (φ δ : ℝ) {N : ℕ} (hδ : 0<δ) (span : (N:ℝ)*δ≤Real.pi) (c : Fin N → ℝ)
    (cells : ∀ j t, (j.val:ℝ)*δ < |t| → |t| ≤ ((j.val:ℝ)+1)*δ →
      c j ≤ (translationLaw W).real (Prod.mk (t-φ) ⁻¹' E)) :
    δ/Real.pi * (∑ j,c j) ≤ (law W).real E := by
  let f (θ : ℝ) := (translationLaw W).real (Prod.mk θ ⁻¹' E)
  have measurableF : Measurable f := (measurable_measure_prodMk_left meas).ennreal_toReal
  have nn (θ) : 0≤f θ := measureReal_nonneg
  have bounded (θ) : f θ ≤ 1 := measureReal_le_one
  have joint : (law W).real E = (2*Real.pi)⁻¹ * ∫ θ in 0..2*Real.pi,f θ := by
    change (((uniformInterval (2*Real.pi)).prod (translationLaw W)) E).toReal=_
    rw [Measure.prod_apply meas,←integral_toReal (measurable_measure_prodMk_left meas).aemeasurable
      (Filter.Eventually.of_forall fun _ => measure_lt_top _ _), integral_uniformInterval (by positivity)]
    rfl
  let g (s : ℝ) := f (s-φ)
  let h (s : ℝ) := g s+g (-s)
  have ig (u : ℝ → ℝ) (m : Measurable u) (a b : ℝ) :
      IntervalIntegrable (f ∘ u) volume a b := by
    apply intervalIntegrable_iff.mpr
    apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne (measurableF.comp m).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun θ => by simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg (nn _)] using bounded (u θ))
  have gp (a b) : IntervalIntegrable g volume a b := ig (fun s => s-φ) (measurable_id.sub_const _) a b
  have gm (a b) : IntervalIntegrable (fun s => g (-s)) volume a b :=
    ig (fun s => -s-φ) (measurable_id.neg.sub_const _) a b
  have hi (a b) : IntervalIntegrable h volume a b := (gp a b).add (gm a b)
  let edge (k : ℕ) : ℝ := k*δ
  have bound (j : Fin N) : 2*δ*c j ≤ ∫ x in edge j.val..edge (j.val+1),h x := by
    let a := edge j.val
    let b := edge (j.val+1)
    have len : b-a=δ := by simp [a,b,edge]; ring
    have a0 : 0≤a := mul_nonneg (Nat.cast_nonneg _) hδ.le
    have ab : a≤b := by linarith
    have z : (∫ _ : ℝ in a..b, 2*c j) ≤ ∫ x in a..b,h x := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo ab intervalIntegrable_const (hi _ _)
      intro x hx
      have pos := a0.trans_lt hx.1
      have bound₁ := cells j x (by simpa [abs_of_pos pos] using hx.1) (by simpa [abs_of_pos pos,b,edge] using hx.2.le)
      have bound₂ := cells j (-x) (by simpa [abs_neg,abs_of_pos pos] using hx.1) (by simpa [abs_neg,abs_of_pos pos,b,edge] using hx.2.le)
      change _ ≤ f (x-φ)+f (-x-φ)
      linarith
    rw [intervalIntegral.integral_const,len,smul_eq_mul] at z
    linarith
  have partition := intervalIntegral.sum_integral_adjacent_intervals (a:=edge) (n:=N)
    (fun j _ => hi (edge j) (edge (j+1)))
  rw [←Fin.sum_univ_eq_sum_range] at partition
  have sectors : 2*δ*(∑ j,c j) ≤ ∫ x in 0..(N:ℝ)*δ,h x := by
    rw [Finset.mul_sum]
    have b := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => bound j)
    exact b.trans_eq (by simpa only [edge,Nat.cast_zero,zero_mul] using partition)
  have expand : (∫ x in 0..Real.pi,h x) = ∫ x in (-Real.pi)..Real.pi,g x := by
    rw [show h=(fun x => g x+g (-x)) from rfl,intervalIntegral.integral_add (gp _ _) (gm _ _),
      intervalIntegral.integral_comp_neg,neg_zero,add_comm,
      intervalIntegral.integral_add_adjacent_intervals (gp _ _) (gp _ _)]
  have window := intervalIntegral.integral_mono_interval (a:=0) (b:=(N:ℝ)*δ) (c:=0) (d:=Real.pi)
    le_rfl (mul_nonneg (Nat.cast_nonneg _) hδ.le) span
    (Filter.Eventually.of_forall fun x => add_nonneg (nn (x-φ)) (nn (-x-φ))) (hi _ _)
  have shifted : (∫ x in (-Real.pi)..Real.pi,g x) = ∫ x in 0..2*Real.pi,f x := by
    rw [show g=(fun x => f (x-φ)) from rfl,intervalIntegral.integral_comp_sub_right]
    have shift := per.intervalIntegral_add_eq (-Real.pi-φ) 0
    simpa only [show -Real.pi-φ+2*Real.pi=Real.pi-φ by ring,zero_add] using shift
  have total := sectors.trans (window.trans_eq (expand.trans shifted))
  rw [joint]
  calc
    δ/Real.pi*(∑ j,c j) = (2*Real.pi)⁻¹*(2*δ*(∑ j,c j)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left total (by positivity)

theorem centreEvent_period (W : Wave.Datum) (X D : Finset Plane) (p : Profile) (v u : Plane) :
    Function.Periodic (fun θ => (translationLaw W).real
      (Prod.mk θ ⁻¹' {ω : Sample | ω.2∈centreEvent W X D p ω.1 v u})) (2*Real.pi) := by
  intro θ
  apply congrArg (translationLaw W).real
  ext τ
  have rot (x : Plane) : rotate (θ+2*Real.pi) x=rotate θ x := by simp [rotate]
  have at' (a : ℝ) : aligned (θ+2*Real.pi) a v u ↔ aligned θ a v u := by simp only [aligned,rot]
  have loc (x : Plane) : place (θ+2*Real.pi,τ) x=place (θ,τ) x := by simp only [place,rot]
  change τ∈centreEvent W X D p (θ+2*Real.pi) v u ↔ τ∈centreEvent W X D p θ v u
  simp only [centreEvent,mem_setOf_eq,candidate,at',loc]

end
end HadwigerNelson.Centres.Events

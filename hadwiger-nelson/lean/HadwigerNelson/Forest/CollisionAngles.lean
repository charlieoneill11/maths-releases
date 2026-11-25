import HadwigerNelson.Forest.UnitAngles
import HadwigerNelson.Stars.RealFourier

/-! For two nearby unit directions, the larger folded angle lies on the
outer side of their ordered pair. The two outer half-windows have the
combined mass of one window. -/

namespace HadwigerNelson.Forest
open Placement MeasureTheory Set Wave Centres
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

private def principal (t : ℝ) : ℝ := (t : Real.Angle).toReal
private def arcPoint (t : ℝ) : Plane := point (-Real.sin t) (Real.cos t)

private theorem chord (s t : ℝ) : dist (arcPoint s) (arcPoint t) ≤ |t-s| := by
  have hcos := Real.cos_two_mul_eq_one_sub ((t-s)/2)
  rw [show 2*((t-s)/2)=t-s by ring,Real.cos_sub] at hcos
  have hsq : dist (arcPoint s) (arcPoint t)^2=(2*|Real.sin ((t-s)/2)|)^2 := by
    rw [coord_dist_sq,mul_pow,sq_abs]
    simp only [arcPoint,point_fst,point_snd]
    linear_combination (Real.sin_sq_add_cos_sq t) + (Real.sin_sq_add_cos_sq s) - 2*hcos
  have eq := (sq_eq_sq₀ dist_nonneg (mul_nonneg (by norm_num) (abs_nonneg _))).mp hsq
  rw [eq]
  have h := Real.abs_sin_le_abs (x:=(t-s)/2)
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)] at h
  linarith only [h]

private theorem phase_chord {φ ψ : ℝ} {x x' y : Plane}
    (hx : ∀ θ,rotate θ (y-x)=arcPoint (θ+φ))
    (hx' : ∀ θ,rotate θ (y-x')=arcPoint (θ+ψ)) (θ : ℝ) :
    dist x x' ≤ |principal (θ+ψ)-principal (θ+φ)| := by
  have same (s) : arcPoint (principal s)=arcPoint s := by
    simp only [arcPoint,principal,Real.Angle.sin_toReal,Real.Angle.cos_toReal,Real.Angle.sin_coe,
      Real.Angle.cos_coe]
  rw [← dist_vsub_cancel_left y x x',← rotate_dist θ]
  change dist (rotate θ (y-x)) (rotate θ (y-x')) ≤ _
  rw [hx,hx',← same (θ+φ),← same (θ+ψ)]
  exact chord _ _

private theorem principal_order {φ ψ θ : ℝ} (hs : 0 ≤ Real.sin (ψ-φ))
    (hφ : |principal (θ+φ)|≤w) (hψ : |principal (θ+ψ)|≤w) :
    principal (θ+φ) ≤ principal (θ+ψ) := by
  have hs' : 0≤Real.sin (principal (θ+ψ)-principal (θ+φ)) := by
    rw [show ψ-φ=(θ+ψ)-(θ+φ) by ring,Real.sin_sub] at hs
    simpa only [Real.sin_sub,principal,Real.Angle.sin_toReal,Real.Angle.cos_toReal,
      Real.Angle.sin_coe,Real.Angle.cos_coe] using hs
  by_contra! rev
  have := Real.sin_neg_of_neg_of_neg_pi_lt (sub_neg.mpr rev) (by
    linarith [(abs_le.mp hφ).2,(abs_le.mp hψ).1,Real.two_le_pi,show w<(1:ℝ) by norm_num [w]])
  linarith

private def outerSide (negative : Bool) (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  if decide (Real.sin t<0) = negative then verticalWindow f t else 0

private theorem side_int (neg : Bool) (f : ℕ → ℝ) (φ : ℝ) :
    Integrable (fun θ => outerSide neg f (θ+φ)) (uniformInterval (2*Real.pi)) := by
  let S := {θ : ℝ | Real.sin (θ+φ)<0}
  have hm : MeasurableSet S := measurableSet_lt (by fun_prop) measurable_const
  have h := verticalWindow_integrable_uniform f φ
  cases neg
  · have eq : (fun θ => outerSide false f (θ+φ)) = Sᶜ.indicator (fun θ => verticalWindow f (θ+φ)) := by
      funext θ
      by_cases yes : Real.sin (θ+φ)<0 <;> simp [outerSide,S,yes]
    rw [eq]; exact h.indicator hm.compl
  · have eq : (fun θ => outerSide true f (θ+φ)) = S.indicator (fun θ => verticalWindow f (θ+φ)) := by
      funext θ
      by_cases yes : Real.sin (θ+φ)<0 <;> simp [outerSide,S,yes]
    rw [eq]; exact h.indicator hm

private theorem side_period (neg : Bool) (f : ℕ → ℝ) :
    Function.Periodic (outerSide neg f) (2*Real.pi) := fun t => by
  simp only [outerSide,Real.sin_add_two_pi,verticalWindow_period f t]

private theorem side_integral_sum (f : ℕ → ℝ) (φ ψ : ℝ) :
    (∫ θ, outerSide true f (θ+φ)+outerSide false f (θ+ψ) ∂uniformInterval (2*Real.pi)) =
      unitBin 1/Real.pi * ∑ k : Fin 16384,f (k.val+1) := by
  rw [integral_add (side_int true f φ) (side_int false f ψ)]
  change Stars.angleMean (fun θ => outerSide true f (θ+φ)) + Stars.angleMean (fun θ => outerSide false f (θ+ψ)) = _
  rw [Stars.angleMean_translate _ (side_period true f) φ,Stars.angleMean_translate _ (side_period false f) ψ]
  change (∫ θ,outerSide true f θ ∂uniformInterval (2*Real.pi)) + (∫ θ,outerSide false f θ ∂uniformInterval (2*Real.pi)) = _
  rw [← integral_add (by simpa using side_int true f 0) (by simpa using side_int false f 0)]
  have together (θ : ℝ) : outerSide true f θ+outerSide false f θ=verticalWindow f θ := by
    by_cases h : Real.sin θ<0 <;> simp [outerSide,h]
  simp_rw [together]
  simpa using verticalWindow_average f 0

private theorem side_nonneg {f : ℕ → ℝ} (hf : ∀ k,0≤f k) (b : Bool) (s : ℝ) :
    0 ≤ outerSide b f s := by
  unfold outerSide verticalWindow
  split
  · split
    · exact hf _
    · rfl
  · rfl

private theorem ordered_density {f : ℕ → ℝ} (hf : ∀ k,0≤f k) {D φ ψ : ℝ} (hD : 0<D)
    (orient : 0≤Real.sin (ψ-φ)) (distance : ∀ θ, D≤|principal (θ+ψ)-principal (θ+φ)|) (θ : ℝ) :
    let g k := if D≤2*unitBin k then f k else 0
    min (verticalWindow f (θ+φ)) (verticalWindow f (θ+ψ)) ≤
      outerSide true g (θ+φ) + outerSide false g (θ+ψ) := by
  intro g
  have hg (k) : 0≤g k := by dsimp only [g]; split <;> first | exact hf _ | rfl
  have nonneg := add_nonneg (side_nonneg hg true (θ+φ)) (side_nonneg hg false (θ+ψ))
  let a := principal (θ+φ)
  let b := principal (θ+ψ)
  have eq (z) : circularDistance z=|principal z| := circularDistance_principal z
  by_cases ha : |a|≤w
  · by_cases hb : |b|≤w
    · have ab : a≤b := principal_order orient ha hb
      have chord' : D≤b-a := by simpa only [a,b,abs_of_nonneg (sub_nonneg.mpr ab)] using distance θ
      have hsa : Real.sin (θ+φ)=Real.sin a := by simp only [a,principal,Real.Angle.sin_toReal,Real.Angle.sin_coe]
      have hsb : Real.sin (θ+ψ)=Real.sin b := by simp only [b,principal,Real.Angle.sin_toReal,Real.Angle.sin_coe]
      by_cases closer : b ≤ -a
      · have aneg : a<0 := by linarith
        have sinneg := Real.sin_neg_of_neg_of_neg_pi_lt aneg (by
          linarith [(abs_le.mp ha).1,Real.two_le_pi,show w<(1:ℝ) by norm_num [w]])
        have enough : D≤2*unitBin (verticalCell |a|) := by
          have bins := (unit_bin_upper ha).2
          rw [abs_of_neg aneg] at bins ⊢
          change -(a) ≤ unitBin (verticalCell (-a)) at bins
          linarith
        apply (min_le_left ..).trans
        apply le_add_of_le_of_nonneg _ (side_nonneg hg false _)
        simp only [outerSide,hsa,sinneg,decide_true,if_true,verticalWindow,eq]
        change (if |a|≤w then f (verticalCell |a|) else 0) ≤ (if |a|≤w then g (verticalCell |a|) else 0)
        simp [ha,g,enough]
      · have bpos : 0≤b := by linarith
        have sinpos := Real.sin_nonneg_of_nonneg_of_le_pi bpos (by
          linarith [(abs_le.mp hb).2,Real.two_le_pi,show w<(1:ℝ) by norm_num [w]])
        have enough : D≤2*unitBin (verticalCell |b|) := by
          have bins := (unit_bin_upper hb).2
          rw [abs_of_nonneg bpos] at bins ⊢
          change b ≤ unitBin (verticalCell b) at bins
          linarith
        apply (min_le_right ..).trans
        apply le_add_of_nonneg_of_le (side_nonneg hg true _) _
        simp only [outerSide,hsb,not_lt.mpr sinpos,decide_false,if_true,verticalWindow,eq]
        change (if |b|≤w then f (verticalCell |b|) else 0) ≤ (if |b|≤w then g (verticalCell |b|) else 0)
        simp [hb,g,enough]
    · apply (min_le_right ..).trans
      simpa only [verticalWindow,eq,show ¬|principal (θ+ψ)|≤w from hb,if_false] using nonneg
  · apply (min_le_left ..).trans
    simpa only [verticalWindow,eq,show ¬|principal (θ+φ)|≤w from ha,if_false] using nonneg

private theorem ordered_mean (f : ℕ → ℝ) (hf : ∀ k,0≤f k) {D φ ψ : ℝ} (hD : 0<D)
    (orient : 0≤Real.sin (ψ-φ)) (distance : ∀ θ, D≤|principal (θ+ψ)-principal (θ+φ)|) :
    (∫ θ, min (verticalWindow f (θ+φ)) (verticalWindow f (θ+ψ)) ∂uniformInterval (2*Real.pi)) ≤
      unitBin 1/Real.pi * ∑ k : Fin 16384,if D≤2*unitBin (k.val+1) then f (k.val+1) else 0 := by
  let g k := if D≤2*unitBin k then f k else 0
  rw [← side_integral_sum g φ ψ]
  apply integral_mono ((verticalWindow_integrable_uniform f φ).inf (verticalWindow_integrable_uniform f ψ))
    ((side_int true g φ).add (side_int false g ψ))
  exact ordered_density hf hD orient distance

theorem collision_mean (W : Wave.Datum) (Ω : ℝ → ℝ → ℝ) (sound : Wave.holeEnclosure W Ω)
    (x x' y : Plane) (hne : x ≠ x') (hx : dist x y = 1) (hx' : dist x' y = 1) :
    (∫ θ, min (edgeUnit Ω θ x y) (edgeUnit Ω θ x' y) ∂uniformInterval (2*Real.pi)) ≤
      unitBin 1/Real.pi * ∑ k : Fin 16384,if dist x x'≤2*unitBin (k.val+1) then unitStep Ω (k.val+1) else 0 := by
  obtain ⟨φ,hφ⟩ := unit_phase hx
  obtain ⟨ψ,hψ⟩ := unit_phase hx'
  simp_rw [fun θ => edgeUnit_phase Ω (hφ θ),fun θ => edgeUnit_phase Ω (hψ θ)]
  by_cases orient : 0≤Real.sin (ψ-φ)
  · exact ordered_mean _ (unitStep_nonneg sound) (dist_pos.mpr hne) orient (phase_chord hφ hψ)
  · have flip : 0≤Real.sin (φ-ψ) := by rw [← neg_sub ψ φ,Real.sin_neg]; linarith
    have h := ordered_mean _ (unitStep_nonneg sound) (dist_pos.mpr hne.symm) flip (phase_chord hψ hφ)
    simpa only [min_comm (verticalWindow _ (_+ψ)),dist_comm x' x] using h

end
end HadwigerNelson.Forest

import HadwigerNelson.Centres.Events.AngularMean
import HadwigerNelson.Centres.Events.Small
import HadwigerNelson.Centres.Events.SmallTranslation
import HadwigerNelson.Centres.Events.MediumPlacement
import HadwigerNelson.Centres.Events.Intervals

namespace HadwigerNelson.Centres.Quadrature
open Set MeasureTheory Placement Wave

noncomputable section

private abbrev event (W : Datum) (X D : Finset Plane) (p : Profile) (v u : Plane) :
    Set Sample := {ω | ω.2∈centreEvent W X D p ω.1 v u}

private theorem below_end {N : Nat} (j : Fin N) {δ t : ℝ} (hδ : 0≤δ)
    (h : |t|≤((j.val:ℝ)+1)*δ) : |t|≤(N:ℝ)*δ := by
  apply h.trans (mul_le_mul_of_nonneg_right _ hδ)
  exact_mod_cast j.isLt

theorem small_probability (W : Datum) (hW : partialProfile W) (X D : Finset Plane)
    (p : Profile) (v u : Plane) (ho : orientation X D v u) (hm : minorArc X u v)
    (hl : chord u v ∈ Icc δR (245/1000)) (ch : chord u v≤2/100)
    (φ : ℝ) (phase : ∀ t, aligned (t-φ) t v u) (checked : smallCheck = true) :
    (if δ≤chord u v then intercept p else smallIntercept p)/2 ≤
      (law W).real (event W X D p v u) := by
  let l := chord u v
  obtain ⟨k,m⟩ := small_match p l
  let s := small k.val
  have ok := smallCheck_each checked k
  have cap := smallPass_real W hW s ok
  have spec := ok
  simp only [smallPass,Bool.and_eq_true,decide_eq_true_eq] at spec
  obtain ⟨⟨⟨⟨⟨_,n⟩,_⟩,lo⟩,_⟩,_⟩ := spec
  have ds : 0<s.dt := by
    unfold Small.dt
    exact div_pos (lt_min (by norm_num) (by change (0:ℚ)<(small k.val).lower/2; positivity)) (by exact_mod_cast n)
  have dstep : 0<angleStep p l := by rw [←m.dt_eq ch]; exact_mod_cast ds
  have npos : 0<(angleBins p:ℝ) := by rw [←m.n]; exact_mod_cast n
  have endEq : (angleBins p:ℝ)*angleStep p l = cone p l := by
    unfold angleStep; field_simp
  let c (j : Fin (angleBins p)) :=
    4*heightStep p/(2*W.x*H) *
      ∑ k : Fin (heightBins p), rectangleHalfWidth W p l (j.val+1) k.val
  have rotation := Events.sector_probability_lower W (event W X D p v u)
    (centreEvent_measurable ..) (Events.centreEvent_period W X D p v u) φ (angleStep p l) dstep
    (endEq ▸ (cone_le_pi p l).le) c (by
      intro j t left right
      have hcone := (below_end j dstep.le right).trans_eq endEq
      have hc : candidate X D p (t-φ) v u := ⟨ho,hm,hl,t,hcone,phase t⟩
      have h := small_translation_bound W X D p (t-φ) t v u hc ch hcone (phase t) dstep.le
      rw [angleBin_eq dstep j left right] at h
      exact h)
  have dtEq : (s.dt:ℝ)=angleStep p l := m.dt_eq ch
  have dyEq : (s.dy:ℝ)=heightStep p := m.dy_eq
  have atCell (j k : Nat) :
      exactWidth W s.lower s.upper ((j+1:Nat)*s.dt) (k*s.dy) s.dy =
      rectangleHalfWidth W p l (j+1) k := by
    simp only [exactWidth,rectangleHalfWidth,
      show (s.lower:ℝ)=_ from m.lo,show (s.upper:ℝ)=_ from m.hi,dtEq,dyEq]
  simp_rw [atCell] at cap
  rw [show s.angles=angleBins p from m.n,show s.heights=heightBins p from m.m,
    show (s.dt:ℝ)=_ from m.dt_eq ch,show (s.dy:ℝ)=_ from m.dy_eq] at cap
  rw [←m.intercept]
  apply (div_le_div_of_nonneg_right cap (by norm_num : (0:ℝ)≤2)).trans
  refine (le_of_eq ?_).trans rotation
  unfold c
  rw [←Finset.mul_sum]
  have hx : W.x ≠0 := by linarith [W.x_bounds.1]
  unfold H
  field_simp
  ring

theorem medium_probability (W : Datum) (hW : partialProfile W) (X D : Finset Plane)
    (p : Profile) (v u : Plane) (ho : orientation X D v u) (hm : minorArc X u v)
    (hl : chord u v ∈ Icc δR (245/1000)) (ch : 2/100<chord u v)
    (φ : ℝ) (phase : ∀ t, aligned (t-φ) t v u) (fine : Bool) (i : Fin 61)
    (a : (breakpoint i.val:ℝ)<chord u v) (b : chord u v≤(breakpoint (i.val+1):ℝ))
    (checked : mediumCheck fine = true) :
    (mTarget fine (breakpoint i.val):ℝ)/2 ≤ (law W).real (event W X D p v u) := by
  let dt := mEnd (breakpoint i.val)/mAngles fine
  have ok := mediumCheck_each checked i
  have spec := ok
  simp only [mediumPass,Bool.and_eq_true,decide_eq_true_eq] at spec
  obtain ⟨⟨_,pos⟩,cap⟩ := spec
  have nd : 0<mAngles fine := by cases fine <;> decide
  have ds : 0<(dt:ℝ) := by exact_mod_cast div_pos pos (show (0:ℚ)<mAngles fine by exact_mod_cast nd)
  have stop : (mAngles fine:ℝ)*(dt:ℝ)=cone p (chord u v) := by
    rw [medium_cone p ch a b]
    dsimp only [dt]; push_cast
    field_simp
  let c (j : Fin (mAngles fine)) : ℝ := mediumTerm fine i.val j.val
  have localBound (j : Fin (mAngles fine)) (t : ℝ) (rt : |t| ≤ ((j.val:ℝ)+1)*(dt:ℝ)) :
      0 ≤ c j ∧ c j≤(translationLaw W).real (centreEvent W X D p (t-φ) v u) := by
    have hcone := (below_end j ds.le rt).trans_eq stop
    have cand : candidate X D p (t-φ) v u := ⟨ho,hm,hl,t,hcone,phase t⟩
    apply mediumTerm_translation W hW X D p _ _ _ _ cand ch (phase t) fine i.val j.val ok b
    convert rt using 1 <;> dsimp [dt] <;> push_cast <;> ring
  have rotation := Events.sector_probability_lower W (event W X D p v u)
    (centreEvent_measurable ..) (Events.centreEvent_period W X D p v u) φ (dt:ℝ) ds
    (stop ▸ (cone_le_pi p _).le) c (fun j t _ rt => (localBound j t rt).2)
  have nn : 0 ≤ ∑ j, c j := Finset.sum_nonneg fun j _ => (localBound j 0 (by simp; positivity)).1
  have h := Rat.cast_le (K:=ℝ) |>.mpr cap
  rw [mediumTotal,Rat.cast_mul,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,cast_array_sum] at h
  change (mTarget fine (breakpoint i.val):ℝ) ≤ 2*(dt:ℝ)/(piHi:ℝ)*(∑ j,c j) at h
  apply (div_le_div_of_nonneg_right h (by norm_num : (0:ℝ)≤2)).trans
  refine (le_of_eq ?_).trans ((mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left ds.le Real.pi_pos angle_upper) nn).trans rotation)
  ring

end
end HadwigerNelson.Centres.Quadrature

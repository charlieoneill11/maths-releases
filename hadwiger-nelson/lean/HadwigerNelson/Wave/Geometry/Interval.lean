import HadwigerNelson.Wave.Geometry
import Mathlib.Topology.Instances.AddCircle.Defs

namespace HadwigerNelson.Wave

noncomputable section

theorem RationalProfile.congr {f g : ℝ → ℝ} (hf : RationalProfile f)
    (h : Set.EqOn g f (Set.Icc 0 H)) : RationalProfile g := by
  obtain ⟨pieces,hp⟩ := hf
  refine ⟨pieces,fun y hy => ?_⟩
  obtain ⟨p,hp,hy',hformula⟩ := hp y hy
  exact ⟨p,hp,hy',fun z hz hz' => (h hz).trans (hformula z hz hz')⟩

theorem zero_rationalProfile : RationalProfile (fun _ => 0) := by
  refine ⟨{(0,1/2,0,0)},fun z hz => ?_⟩
  refine ⟨(0,1/2,0,0),by simp,?_,?_⟩
  · simpa [H] using hz
  · simp

/-- Continuous periodic extension of a reflected tile profile. The last component
chooses one representative for a point and all its translates. -/
private theorem extend_symmetric (r0 : ℝ → ℝ) (hc : ContinuousOn r0 (Set.Icc 0 H))
    (hs : ∀ y ∈ Set.Icc 0 H, r0 (H-y)=r0 y) :
    ∃ r : ℝ → ℝ, Continuous r ∧ Function.Periodic r H ∧ (∀ y,r (-y)=r y) ∧
      Set.EqOn r r0 (Set.Icc 0 H) ∧
      ∀ y, ∃ v ∈ Set.Ico 0 H, ∀ t, r (y+t)=r (v+t) := by
  have hh := H_pos
  letI : Fact (0 < H) := ⟨hh⟩
  let R : AddCircle H → ℝ := AddCircle.liftIco H 0 r0
  let r : ℝ → ℝ := fun t => R (t : AddCircle H)
  have ep : r0 0 = r0 H := by
    simpa using (hs 0 ⟨le_rfl,hh.le⟩).symm
  have hcont : Continuous r := (AddCircle.liftIco_zero_continuous ep hc).comp (AddCircle.continuous_mk' H)
  have hper : Function.Periodic r H := fun y => congrArg R (AddCircle.coe_add_period H y)
  have eqn : Set.EqOn r r0 (Set.Icc 0 H) := by
    intro y hy
    rcases hy.2.eq_or_lt with rfl | hy'
    · change R (H : AddCircle H) = _
      rw [AddCircle.coe_period]
      exact (AddCircle.liftIco_zero_coe_apply (f:=r0) ⟨by rfl,hh⟩).trans ep
    · exact AddCircle.liftIco_zero_coe_apply ⟨hy.1,hy'⟩
  have reduce (y : ℝ) : ∃ v ∈ Set.Ico 0 H, (v : AddCircle H) = (y : AddCircle H) :=
    AddCircle.eq_coe_Ico _
  have hev (y : ℝ) : r (-y) = r y := by
    obtain ⟨v,hv,e⟩ := reduce y
    have e1 : ((H-v : ℝ) : AddCircle H) = ((-y : ℝ) : AddCircle H) := by
      rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub, e, AddCircle.coe_neg]
    have h1 : H-v ∈ Set.Icc 0 H := ⟨sub_nonneg.mpr hv.2.le,sub_le_self _ hv.1⟩
    exact (congrArg R e1).symm.trans <| (eqn h1).trans <| (hs v ⟨hv.1,hv.2.le⟩).trans <|
      (eqn ⟨hv.1,hv.2.le⟩).symm.trans (congrArg R e)
  refine ⟨r,hcont,hper,hev,eqn,fun y => ?_⟩
  obtain ⟨v,hv,e⟩ := reduce y
  refine ⟨v,hv,fun t => congrArg R ?_⟩
  simp only [AddCircle.coe_add,e]

/-- Periodically extend a rational complete-wave profile given on [0,H]. -/
theorem complete_of_interval (xq : ℚ) (r0 : ℝ → ℝ)
    (hx : 9/10 < (xq:ℝ) ∧ (xq:ℝ)<1) (hr : RationalProfile r0)
    (hc : ContinuousOn r0 (Set.Icc 0 H))
    (hs : ∀ y ∈ Set.Icc 0 H, r0 (H-y)=r0 y)
    (hp : ∀ y ∈ Set.Icc 0 (H/2), r0 y+r0 (y+H/2)=2*(xq:ℝ))
    (hb : ∀ y ∈ Set.Icc 0 H, 4/5 < r0 y ∧ r0 y < 1) :
    ∃ W : Datum, W.x=(xq:ℝ) ∧ W.left=(fun _ => 0) ∧ W.y0=0 ∧ Set.EqOn W.right r0 (Set.Icc 0 H) := by
  have hh := H_pos
  obtain ⟨r,hcont,hper,hev,eqn,reduce⟩ := extend_symmetric r0 hc hs
  have hstep (v : ℝ) (hv : v ∈ Set.Icc 0 (H/2)) : r v + r (v+H/2)=2*(xq:ℝ) := by
    rw [eqn (show v ∈ Set.Icc 0 H from ⟨hv.1,by linarith [hv.2]⟩),
      eqn (show v+H/2 ∈ Set.Icc 0 H from ⟨by linarith [hv.1],by linarith [hv.2]⟩)]
    exact hp v hv
  have hcomp (y : ℝ) : r y + r (y+H/2)=2*(xq:ℝ) := by
    obtain ⟨v,hv,e⟩ := reduce y
    have e0 := e 0
    simp only [add_zero] at e0
    rw [e0,e (H/2)]
    by_cases hv' : v ≤ H/2
    · exact hstep v ⟨hv.1,hv'⟩
    · have h2 := hstep (v-H/2) ⟨by linarith,by linarith [hv.2]⟩
      rw [sub_add_cancel] at h2
      rw [show v+H/2=(v-H/2)+H by ring, hper, add_comm]
      exact h2
  have hbounds (y : ℝ) : 4/5 < r y ∧ r y < 1 := by
    obtain ⟨v,hv,e⟩ := reduce y
    have e0 := e 0
    simp only [add_zero] at e0
    rw [e0,eqn ⟨hv.1,hv.2.le⟩]
    exact hb v ⟨hv.1,hv.2.le⟩
  let W : Datum := {
    x := xq, x_rational := ⟨xq,rfl⟩, x_bounds := hx
    left := fun _ => 0, right := r
    left_rational := zero_rationalProfile, right_rational := hr.congr eqn
    left_continuous := continuous_const, right_continuous := hcont
    left_periodic := fun _ => rfl, right_periodic := hper
    left_even := fun _ => rfl, right_even := hev, complement := hcomp
    left_antitone := fun _ _ _ _ _ => le_rfl
    y0 := 0, y0_bounds := ⟨le_rfl,by linarith⟩, left_zero := fun _ _ => rfl
    left_bounds := fun _ => ⟨le_rfl,by norm_num⟩, right_bounds := hbounds }
  exact ⟨W,rfl,rfl,rfl,eqn⟩

/-- Extend both profiles of a partial wave, carrying the cutoff and the exact
real functions on the closed tile interval into the result. -/
theorem partial_of_interval (xq : ℚ) (y0 : ℝ) (l0 r0 : ℝ → ℝ)
    (hx : 9/10 < (xq:ℝ) ∧ (xq:ℝ)<1) (hy0 : 0 ≤ y0 ∧ y0 < H/4)
    (lr : RationalProfile l0) (rr : RationalProfile r0)
    (lc : ContinuousOn l0 (Set.Icc 0 H)) (rc : ContinuousOn r0 (Set.Icc 0 H))
    (ls : ∀ y ∈ Set.Icc 0 H, l0 (H-y)=l0 y) (rs : ∀ y ∈ Set.Icc 0 H, r0 (H-y)=r0 y)
    (rp : ∀ y ∈ Set.Icc 0 (H/2), r0 y+r0 (y+H/2)=2*(xq:ℝ))
    (lb : ∀ y ∈ Set.Icc 0 H, 0 ≤ l0 y ∧ l0 y < 1/5)
    (rb : ∀ y ∈ Set.Icc 0 H, 4/5 < r0 y ∧ r0 y < 1)
    (lanti : AntitoneOn l0 (Set.Icc 0 (H/2))) (zero : ∀ y ∈ Set.Icc y0 (H/2), l0 y = 0) :
    ∃ W : Datum, W.x=(xq:ℝ) ∧ W.y0=y0 ∧ Set.EqOn W.left l0 (Set.Icc 0 H) ∧
      Set.EqOn W.right r0 (Set.Icc 0 H) := by
  obtain ⟨W,wx,_,_,right⟩ := complete_of_interval xq r0 hx rr rc rs rp rb
  obtain ⟨l,hc,hp,hs,eqn,red⟩ := extend_symmetric l0 lc ls
  have hh := H_pos
  have sub : Set.Icc 0 (H/2) ⊆ Set.Icc 0 H := fun _ h => ⟨h.1,by linarith [h.2]⟩
  let W' : Datum := { W with
    left := l, left_rational := lr.congr eqn, left_continuous := hc, left_periodic := hp,
    left_even := hs, left_antitone := fun a ha b hb le => by rw [eqn (sub ha),eqn (sub hb)]; exact lanti ha hb le
    y0 := y0, y0_bounds := hy0
    left_zero := fun y hy => by rw [eqn (sub ⟨hy0.1.trans hy.1,hy.2⟩)]; exact zero y hy
    left_bounds := fun y => by
      obtain ⟨v,hv,e⟩ := red y
      have e0 := e 0
      simp only [add_zero] at e0
      rw [e0,eqn ⟨hv.1,hv.2.le⟩]
      exact lb v ⟨hv.1,hv.2.le⟩ }
  exact ⟨W',wx,rfl,eqn,right⟩

end

end HadwigerNelson.Wave

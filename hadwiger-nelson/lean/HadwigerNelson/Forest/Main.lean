import HadwigerNelson.Forest.HeadMean
import HadwigerNelson.Blueprint.Point.CentreEvents
import HadwigerNelson.Blueprint.Point.PartialConstants

namespace HadwigerNelson.Forest
open MeasureTheory Set Placement Crossings Centres Certificate
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev scale : ℝ := 10^18
private abbrev B : ℝ := 112668096940/scale
private abbrev C : ℝ := 16034576942481/scale
private abbrev E : ℝ := 3057937052494/scale

/-- Combine the two centre profiles after the three forest modes. The
same centre term is subtracted from each of the three expected costs. -/
private theorem assemble_objective (n m s j : ℕ) (rD rR Rloss : ℝ)
    (rval : rR=weightedBound n m s j (828/1000) (1195/10000))
    (dval : rD=weightedBound n m s j (828/1000) (6195/10000))
    (loss : Rloss=(min ((n-s:ℕ)*(150296106235:ℝ)) (min ((n-s:ℕ)*(97911102803:ℝ)+j*104770006866) (j*(300592212470:ℝ))))/scale)
    (bounds : ∀ p : Profile, let cr := profileCredit n m s j (intercept p) (smallIntercept p) (angleCost p)
      let upper := n*(71152801254159/scale:ℝ)+m*(708385488148/scale:ℝ)
      1+cr≤upper ∧ 1+cr+(s:ℝ)*C+j*E+B*(m-rR)-Rloss≤upper ∧
      1+cr+(s:ℝ)*C+j*E+B*(m-rD)≤upper) :
    1≤pointObjective n m s j := by
  subst rR rD Rloss
  let cr := fun p : Profile => profileCredit n m s j (intercept p) (smallIntercept p) (angleCost p)
  have pick : ∃ p : Profile,centreCredit n m s j=cr p := by
    by_cases q : cr .coarse≤cr .fine
    · exact ⟨.fine,max_eq_right q⟩
    · exact ⟨.coarse,max_eq_left (le_of_not_ge q)⟩
  obtain ⟨p,eq⟩ := pick
  obtain ⟨base,outer,inner⟩ := bounds p
  unfold pointObjective
  rw [eq,le_sub_iff_add_le,le_div_iff₀ (by positivity)]
  apply le_min
  · dsimp only [cr]; linarith only [base]
  · apply le_min
    · dsimp only [cr]; linarith only [outer]
    · dsimp only [cr]; linarith only [inner]

/-- Proposition 44 with both nested sets, all unit edges, and the same
numerical objective that occurs in Proposition 53. -/
theorem main_inequality (facts : CitedFacts) (X R D : Finset Plane)
    (hn : 2090 ≤ X.card) (hd : Crossings.minNonisolatedDegree X 6)
    (noncolourable : ¬ ∃ c : Plane → Fin 6, ∀ x ∈ X, ∀ y ∈ X, dist x y = 1 → c x ≠ c y)
    (hR : maximalSeparated X R (53/10000)) (hD : maximalSeparated R D (1837/250000)) :
    1 ≤ Certificate.pointObjective X.card (Crossings.unitEdgeCount X) (X.card-R.card) (R.card-D.card) := by
  classical
  let W := PartialWave.datum
  have full := datum_fullPartialProfile
  have hw : partialProfile W := full.1
  let Ω := partialOmega W
  have sound : Wave.holeEnclosure W Ω := partialOmega_sound W hw
  have hd3 : minNonisolatedDegree X 3 := fun x hx => (hd x hx).imp_right (by omega)
  obtain ⟨L,rfl,rfl⟩ := layers_for X R D hR hD
  let n := X.card
  let m := unitEdgeCount X
  let s := X.card-L.R.card
  let j := L.R.card-L.D.card
  let rR := weightedBound n m s j (828/1000) (1195/10000)
  let rD := weightedBound n m s j (828/1000) (6195/10000)
  let Rloss := (min ((n-s:ℕ)*(150296106235:ℝ))
    (min ((n-s:ℕ)*(97911102803:ℝ)+j*104770006866) (j*(300592212470:ℝ))))/scale
  have rcard : n-s=L.R.card := by have := Finset.card_le_card L.maximalR.1; dsimp only [n,s]; omega
  obtain ⟨bm,cm,em,lu,tu,uu,ju,ra,rd⟩ := partialConstants W hw
  have blank : blankDensity W≤71152801254159/scale := by rw [partial_blank_density W hw]; norm_num [scale]
  have mono : meanMonoProb W-(901/10^12)/2≤708385488148/scale := by
    calc _ ≤ 102782566719698111/145001902327661557000000-(901/10^12)/2 :=
               sub_le_sub_right (partial_mono_probability W full) _
         _ ≤ _ := by norm_num [scale]
  let ub : ℝ := n*(71152801254159/scale:ℝ)+m*(708385488148/scale:ℝ)
  let S (mode) := ∫ θ,∑ y∈X,edgeShort L Ω mode θ y ∂uniformInterval (2*Real.pi)
  let U (mode) := ∫ θ,∑ y∈X,excessCredit L Ω mode θ y ∂uniformInterval (2*Real.pi)
  let K (mode) := ∫ θ,∑ y∈X,collisionLoss L Ω mode θ y ∂uniformInterval (2*Real.pi)
  have shared (p : Profile) (mode : Mode) :
      1+S mode+U mode-K mode+profileCredit n m s j (intercept p) (smallIntercept p) (angleCost p)≤ub := by
    have term := mean_head_budget W hw Ω sound X L mode p
    have centre := credit_lower facts W hw X L.R L.D hn hd3 hR hD p
    have score := score_from_heads W X L mode p (candidate_measurable X L.D p) noncolourable (901/10^12)
      (fun edges unit v => Stars.partial_locked W full Proof.palette edges unit v)
    have up : X.card*blankDensity W + unitEdgeCount X*(meanMonoProb W-(901/10^12)/2)≤ub :=
      add_le_add (mul_le_mul_of_nonneg_left blank (by positivity)) (mul_le_mul_of_nonneg_left mono (by positivity))
    have u := score.trans up
    change S mode+U mode-K mode+_ ≤ _ at term
    dsimp only [n,m,s,j]
    linarith only [u,term,centre]
  have short (mode : Mode) (on : mode≠.centresOnly) : (s:ℝ)*C+j*E≤S mode :=
    short_payment sound L mode on C E cm em
  have br : B*((m:ℝ)-rR)≤U .r := unit_payment facts sound L .r (by decide) B (by norm_num [B,scale]) bm ra rd hn hd3
  have bd : B*((m:ℝ)-rD)≤U .d := unit_payment facts sound L .d (by decide) B (by norm_num [B,scale]) bm ra rd hn hd3
  have ci : K .d=0 := by simp only [K,collision_inner_zero,Finset.sum_const_zero,integral_zero]
  have cr : K .r≤Rloss := by
    have geom := (collisionR_total W Ω sound X L).trans (collision_constants W Ω sound X L)
    apply geom.trans
    dsimp only [Rloss]
    rw [rcard]
    rw [← min_div_div_right (by positivity : (0:ℝ)≤scale),← min_div_div_right (by positivity : (0:ℝ)≤scale)]
    apply min_le_min
    · simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left lu (show 0≤(L.R.card:ℝ) by positivity)
    · apply min_le_min
      · rw [add_div,mul_div_assoc,mul_div_assoc]
        exact add_le_add (mul_le_mul_of_nonneg_left tu (by positivity)) (mul_le_mul_of_nonneg_left uu (by positivity))
      · simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left ju (show 0≤(j:ℝ) by positivity)
  apply assemble_objective n m s j rD rR Rloss rfl rfl rfl
  intro p
  have no := shared p .centresOnly
  have r := shared p .r
  have d := shared p .d
  have sn : S .centresOnly=0 := by simp [S,edgeShort]
  have un : U .centresOnly=0 := by simp [U,excessCredit,eligible]
  have kn : K .centresOnly=0 := by simp [K,collisionLoss,eligible]
  rw [sn,un,kn] at no
  rw [ci] at d
  dsimp only [ub] at no r d
  refine ⟨by linarith only [no],?_,?_⟩
  · have pay := sub_le_sub (add_le_add (short .r (by decide)) br) cr
    let cn := profileCredit n m s j (intercept p) (smallIntercept p) (angleCost p)
    calc _ = (1+cn)+((s*C+j*E+B*(m-rR))-Rloss) := by dsimp only [cn]; ring
         _ ≤ (1+cn)+((S .r+U .r)-K .r) := add_le_add_right pay _
         _ = 1+S .r+U .r-K .r+cn := by ring
         _ ≤ _ := r
  · have pay := add_le_add (short .d (by decide)) bd
    let cn := profileCredit n m s j (intercept p) (smallIntercept p) (angleCost p)
    calc _ = (1+cn)+(s*C+j*E+B*(m-rD)) := by dsimp only [cn]; ring
         _ ≤ (1+cn)+(S .d+U .d) := add_le_add_right pay _
         _ = 1+S .d+U .d-0+cn := by ring
         _ ≤ _ := d

end
end HadwigerNelson.Forest

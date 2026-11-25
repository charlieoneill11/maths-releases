import HadwigerNelson.Forest.PlacementScore
import HadwigerNelson.Forest.ModeMeans
import HadwigerNelson.Forest.CollisionTotal
import HadwigerNelson.Blueprint.Point.Forest
import HadwigerNelson.Centres.BudgetDefs
import HadwigerNelson.Wave.Geometry.PartialProfile
import HadwigerNelson.Centres.Events.Measurable

namespace HadwigerNelson.Forest
open Placement MeasureTheory Set Centres Crossings
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Fubini for the real probability of a measurable joint event, including
integrability of its translation-conditional probability as a function of rotation. -/
private theorem section_mean (W : Wave.Datum) (A : Set Sample) (meas : MeasurableSet A) :
    let q := fun θ => (translationLaw W).real (Prod.mk θ ⁻¹' A)
    Integrable q (uniformInterval (2*Real.pi)) ∧ (∫ θ,q θ ∂uniformInterval (2*Real.pi))=(law W).real A := by
  intro q
  let f := A.indicator (1 : Sample → ℝ)
  have hi : Integrable f ((uniformInterval (2*Real.pi)).prod (translationLaw W)) := (integrable_const 1).indicator meas
  have val (θ) : (∫ τ,f (θ,τ) ∂translationLaw W)=q θ := by
    rw [show q θ = (translationLaw W).real (Prod.mk θ ⁻¹' A) from rfl,← integral_indicator_one (meas.preimage measurable_prodMk_left)]
    apply integral_congr_ae; exact Filter.Eventually.of_forall (fun τ => by
      by_cases h : (θ,τ)∈A <;> simp [f,h])
  have I := hi.integral_prod_left
  have avg := integral_prod f hi
  simp_rw [val] at I avg
  exact ⟨I,avg.symm.trans (integral_indicator_one meas)⟩

theorem mean_head_budget (W : Wave.Datum) (hW : partialProfile W) (Ω : ℝ → ℝ → ℝ) (sound : Wave.holeEnclosure W Ω)
    (X : Finset Plane) (L : Layers X) (m : Mode) (p : Profile) :
    (∫ θ,∑ y∈X,edgeShort L Ω m θ y ∂uniformInterval (2*Real.pi)) +
    (∫ θ,∑ y∈X,excessCredit L Ω m θ y ∂uniformInterval (2*Real.pi)) -
    (∫ θ,∑ y∈X,collisionLoss L Ω m θ y ∂uniformInterval (2*Real.pi)) +
    (∑ z∈orientationSet X L.D δR,(law W).real {ω : Sample | ω.2∈centreEvent W X L.D p ω.1 z.1 z.2}) ≤
      ∑ y∈X,(law W).real (headEvent W L m p y) := by
  let μ := uniformInterval (2*Real.pi)
  let P (v y : Plane) := {ω : Sample | ω.2∈centreEvent W X L.D p ω.1 v y}
  let c := fun v y θ => (translationLaw W).real (Prod.mk θ ⁻¹' P v y)
  let h := fun y θ => (translationLaw W).real (Prod.mk θ ⁻¹' headEvent W L m p y)
  have cM (v y) : Integrable (c v y) μ ∧ (∫ θ,c v y θ ∂μ)=(law W).real (P v y) :=
    section_mean W (P v y) (centreEvent_measurable W X L.D p v y)
  have hM (y) : Integrable (h y) μ ∧ (∫ θ,h y θ ∂μ)=(law W).real (headEvent W L m p y) :=
    section_mean W _ (headEvent_measurable W L m p (candidate_measurable X L.D p) y)
  let s (θ : ℝ) := ∑ y∈X,edgeShort L Ω m θ y
  let e (θ : ℝ) := ∑ y∈X,excessCredit L Ω m θ y
  let l (θ : ℝ) := ∑ y∈X,collisionLoss L Ω m θ y
  let a (θ : ℝ) := ∑ y∈X,∑ v∈X,c v y θ
  let b (θ : ℝ) := ∑ y∈X,h y θ
  have si : Integrable s μ := integrable_finset_sum X (fun y _ => short_integrable sound L m y)
  have ei : Integrable e μ := integrable_finset_sum X (fun y _ => excess_integrable L Ω m y (fun x => edgeUnit_integrable Ω x y))
  have li : Integrable l μ := integrable_finset_sum X (fun y _ => collisionLoss_int L Ω m y)
  have ci (y) := integrable_finset_sum X (fun v _ => (cM v y).1)
  have ai : Integrable a μ := integrable_finset_sum X (fun y _ => ci y)
  have bi : Integrable b μ := integrable_finset_sum X (fun y _ => (hM y).1)
  have point (θ) : s θ+e θ-l θ+a θ≤b θ := by
    have each (y) (hy : y∈X) : edgeShort L Ω m θ y+excessCredit L Ω m θ y-collisionLoss L Ω m θ y+
        (∑ v∈X,c v y θ)≤h y θ := head_credit_lower W hW Ω sound X L m p θ y hy
    simpa only [s,e,l,a,b,Finset.sum_add_distrib,Finset.sum_sub_distrib] using Finset.sum_le_sum each
  have pay := integral_mono (((si.add ei).sub li).add ai) bi point
  change (∫ θ,(s θ+e θ-l θ)+a θ ∂μ) ≤ ∫ θ,b θ ∂μ at pay
  have addi : Integrable (fun θ => s θ+e θ) μ := si.add ei
  have subi : Integrable (fun θ => s θ+e θ-l θ) μ := addi.sub li
  rw [integral_add subi ai,integral_sub addi li,integral_add si ei] at pay
  have hmean : (∫ θ,b θ ∂μ)=∑ y∈X,(law W).real (headEvent W L m p y) := by
    rw [show b=fun θ => ∑ y∈X,h y θ from rfl,integral_finset_sum X (fun y _ => (hM y).1)]
    exact Finset.sum_congr rfl (fun y _ => (hM y).2)
  have cmean : (∫ θ,a θ ∂μ)=∑ y∈X,∑ v∈X,(law W).real (P v y) := by
    rw [show a=fun θ => ∑ y∈X,∑ v∈X,c v y θ from rfl,integral_finset_sum X (fun y _ => ci y)]
    apply Finset.sum_congr rfl; intro y _
    rw [integral_finset_sum X (fun v _ => (cM v y).1)]
    exact Finset.sum_congr rfl (fun v _ => (cM v y).2)
  rw [cmean,hmean] at pay
  have sub : orientationSet X L.D δR⊆X×ˢX := by
    intro z hz
    have ze := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
    exact Finset.mem_product.mpr ⟨ze.1,L.maximalR.1 (L.maximalD.1 ze.2)⟩
  have kept := Finset.sum_le_sum_of_subset_of_nonneg (f:=fun z : Plane×Plane => (law W).real (P z.1 z.2))
    sub (fun _ _ _ => measureReal_nonneg)
  rw [Finset.sum_product,Finset.sum_comm] at kept
  exact (add_le_add_right kept _).trans pay

end
end HadwigerNelson.Forest

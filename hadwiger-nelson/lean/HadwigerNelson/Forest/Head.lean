import HadwigerNelson.Forest.HeadEvents

namespace HadwigerNelson.Forest
open Placement MeasureTheory Set Centres
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A zero-credit noncandidate has an empty event. This convention retains
all tail indices in the sums for both choices of eligible layer. -/
private def unitEvent (W : Wave.Datum) (θ : ℝ) (v y : Plane) : Set Translation :=
  {t | unitCandidate θ v y ∧ t∈pairBlanks W θ v y}

private theorem unitEvent_paid (W : Wave.Datum) (Ω : ℝ → ℝ → ℝ) (θ : ℝ) (v y : Plane)
    (credit : ∀ s : ℝ, |s| ≤ w →
      unitCredit Ω s ≤ Wave.bothBlank W (Wave.point (Real.sin s) (Real.cos s))) :
    edgeUnit Ω θ v y ≤ (translationLaw W).real (unitEvent W θ v y) := by
  by_cases cand : unitCandidate θ v y
  · obtain ⟨s,hs,disp⟩ := cand
    have he : unitEvent W θ v y=pairBlanks W θ v y := by ext t; simp [unitEvent,show unitCandidate θ v y from ⟨s,hs,disp⟩]
    have sw := abs_le.mp hs
    have recover : Real.arcsin (Real.sin s)=s := Real.arcsin_sin
      (by linarith [sw.1,Real.two_le_pi,show w≤1 by norm_num [w]])
      (by linarith [sw.2,Real.two_le_pi,show w≤1 by norm_num [w]])
    rw [he,pairBlanks_probability,edgeUnit,if_pos (show unitCandidate θ v y from ⟨s,hs,disp⟩),disp,Wave.point_fst,recover]
    exact credit s hs
  · have empty : unitEvent W θ v y=∅ := by ext t; simp [unitEvent,cand]
    simp [edgeUnit,cand,empty]

theorem head_credit_from_geometry (W : Wave.Datum) (hW : partialProfile W) (Ω : ℝ → ℝ → ℝ)
    (sound : Wave.holeEnclosure W Ω) (X : Finset Plane) (L : Layers X) (m : Mode)
    (p : Profile) (θ : ℝ) (y : Plane) (hy : y∈X)
    (short_bound : ∀ ρ v, 0<‖v‖ → ‖v‖≤2*ρ → lowerShort Ω ρ (shortIndex v) ≤ Wave.bothBlank W v)
    (unit_bound : ∀ t : ℝ, |t| ≤ w → unitCredit Ω t ≤ Wave.bothBlank W (Wave.point (Real.sin t) (Real.cos t)))
    (unique : ∀ v u, candidate X L.D p θ v y → candidate X L.D p θ u y → v=u)
    (clean : ∀ v, ∀ᵐ t ∂translationLaw W, t∈centreEvent W X L.D p θ v y →
      colour W (θ,t) y=none ∧ colour W (θ,t) v=none ∧
      ∀ x∈X,unitCandidate θ x y → (colour W (θ,t) x).isSome=true) :
    edgeShort L Ω m θ y + excessCredit L Ω m θ y - collisionLoss L Ω m θ y +
      (∑ v∈X,(translationLaw W).real (centreEvent W X L.D p θ v y)) ≤
    (translationLaw W).real {t | ∃ x∈X, allCandidates L m p θ x y ∧
      colour W (θ,t) x=none ∧ colour W (θ,t) y=none} := by
  classical
  let C := fun v => centreEvent W X L.D p θ v y
  let μ := translationLaw W
  let S := eligible L m
  let E := fun i => unitEvent W θ i y
  let H := fun i => edgeUnit Ω θ i y
  let active := m ≠ .centresOnly ∧ y∉L.D
  let Q := if active then pairBlanks W θ (L.parent y) y else ∅
  let A := {t | ∃ x∈X,allCandidates L m p θ x y ∧ colour W (θ,t) x=none ∧ colour W (θ,t) y=none}
  have sx (i) (hi : i∈S) : i∈X := by
    cases m with
    | r => exact L.maximalR.1 hi
    | d => exact L.maximalR.1 (L.maximalD.1 hi)
    | centresOnly => exact False.elim (Finset.notMem_empty _ hi)
  have sm (i) (hi : i∈S) : m ≠ .centresOnly := by
    rintro rfl; exact Finset.notMem_empty _ hi
  have ms : MeasurableSet Q := by
    dsimp only [Q]; split
    · apply pairBlanks_measurable
    · exact MeasurableSet.empty
  have me (i) : MeasurableSet (E i) := by
    by_cases h : unitCandidate θ i y
    · simpa [E,unitEvent,h] using pairBlanks_measurable W θ i y
    · simp [E,unitEvent,h]
  have spaid : edgeShort L Ω m θ y ≤ μ.real Q := by
    by_cases act : active
    · obtain ⟨_,neq,near⟩ := parent_edge L hy act.2
      let v := rotate θ (y-L.parent y)
      have norm : ‖v‖=dist y (L.parent y) := by
        rw [← rotate_dist θ,dist_eq_norm,← rotate_sub]
      have bound := short_bound _ v (norm ▸ dist_pos.mpr neq) (norm ▸ near)
      rw [show Q=pairBlanks W θ (L.parent y) y from if_pos act]
      exact (min_le_left ..).trans (bound.trans_eq (pairBlanks_probability W θ (L.parent y) y).symm) |>
        (fun h => by simpa [edgeShort,act.1,act.2,cappedShort,v,μ] using h)
    · have off : m=.centresOnly ∨ y∈L.D := by dsimp [active] at act; tauto
      simp [edgeShort,off,Q,act]
  have ex (i) (_ : i∈S) (hi : i∈L.D) (j) (_ : j∈S) (hj : j∈L.D) (ne : i≠j) :
      AEDisjoint μ (E i) (E j) := by
    by_cases ci : unitCandidate θ i y
    · by_cases cj : unitCandidate θ j y
      · apply ae_disjoint_of_event
        filter_upwards [two_inner_tails W hW L.D L.maximalD.2.1 i j y hi hj ne θ ci cj] with t ht
        exact fun h => ht ⟨h.1.2.1,h.2.2.1⟩
      · exact (show Disjoint (E i) (E j) by simp [E,unitEvent,cj]).aedisjoint
    · exact (show Disjoint (E i) (E j) by simp [E,unitEvent,ci]).aedisjoint
  have ready := edgeShort_bounds sound L m θ y
  have local_bound (Z : Set Translation)
      (sep : ∀ᵐ t ∂μ, t∈Z → t∉Q ∧ ∀ i∈S,t∉E i)
      (inc : ∀ᵐ t ∂μ, t∈Z → t∈A) :
      edgeShort L Ω m θ y + excessCredit L Ω m θ y - collisionLoss L Ω m θ y +
        μ.real Z ≤ μ.real A := by
    have cover : ∀ᵐ t ∂μ, (t∈Q ∨ (∃ i∈S,t∈E i) ∨ t∈Z) → t∈A := by
      filter_upwards [inc] with t ht
      rintro (hq|⟨i,hi,ei⟩|hz)
      · by_cases ac : active
        · have q : t∈pairBlanks W θ (L.parent y) y := by simpa [Q,ac] using hq
          exact ⟨_,(parent_edge L hy ac.2).1,Or.inl ⟨ac.1,Or.inl ⟨ac.2,rfl⟩⟩,q⟩
        · simp [Q,ac] at hq
      · exact ⟨_,sx _ hi,Or.inl ⟨sm _ hi,Or.inr ⟨hi,ei.1⟩⟩,ei.2⟩
      · exact ht hz
    convert head_events_bound S L.D H Q Z A E (edgeShort L Ω m θ y) (headCap L Ω y)
      ready.1 ready.2 (fun i _ => edgeUnit_nonneg sound θ i y) ms (fun i _ => me i) spaid
      (fun i _ => unitEvent_paid W Ω θ i y unit_bound) ex sep cover using 1
  by_cases found : ∃ v∈X,candidate X L.D p θ v y
  · obtain ⟨v,hv,hc⟩ := found
    have sum : (∑ i∈X,μ.real (C i))=μ.real (C v) := by
      apply Finset.sum_eq_single_of_mem v hv
      intro j _ ne
      have emp : C j=∅ := Set.eq_empty_iff_forall_notMem.mpr fun t h => ne (unique j v h.1 hc)
      simp [emp]
    rw [show (∑ i∈X,(translationLaw W).real (centreEvent W X L.D p θ i y))=μ.real (C v) from sum]
    apply local_bound
    · filter_upwards [clean v] with t ht
      intro hz
      obtain ⟨_,_,block⟩ := ht hz
      have off : ¬active := fun act => act.2 hc.1.2.1
      refine ⟨by simp [Q,off],?_⟩
      intro i hi he
      have neq := block i (sx i hi) he.1
      rw [he.2.1] at neq
      contradiction
    · filter_upwards [clean v] with t ht
      intro hz
      exact ⟨v,hv,Or.inr hc,(ht hz).2.1,(ht hz).1⟩
  · have sum : (∑ i∈X,μ.real (C i))=0 := Finset.sum_eq_zero (fun i hi => by
      have emp : C i=∅ := Set.eq_empty_iff_forall_notMem.mpr fun t h => found ⟨_,hi,h.1⟩
      simp [emp])
    rw [show (∑ i∈X,(translationLaw W).real (centreEvent W X L.D p θ i y))=0 from sum]
    simpa using local_bound ∅ (by simp) (by simp)

end
end HadwigerNelson.Forest

import HadwigerNelson.Crossings.UnitArcDrawing
import HadwigerNelson.Crossings.Subsets
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Intersections of consecutive unit-circle arcs counted by their two circle centres. -/
namespace HadwigerNelson.Crossings
open Finset Set
noncomputable section
attribute [local instance] Classical.propDecidable
variable {X : Finset Plane}

private theorem pair_points (P : Finset Plane) (h : P.card = 2) :
    ∃ T : Finset Plane, T.card ≤ 2 ∧ ∀ z, z ∈ T ↔ ∀ v ∈ P, dist z v = 1 := by
  obtain ⟨a,b,ne,rfl⟩ := Finset.card_eq_two.mp h
  obtain ⟨T,ht,spec⟩ := unit_intersections_le_two a b ne
  exact ⟨T,ht,fun z ↦ by simpa using spec z⟩

private def meeting (P : Finset Plane) : Finset Plane :=
  if h : P.card=2 then (pair_points P h).choose else ∅

private theorem meet_spec (P : Finset Plane) (h : P.card=2) : (meeting P).card ≤ 2 ∧
    ∀ z, z ∈ meeting P ↔ ∀ v ∈ P, dist z v = 1 := by
  rw [meeting,dif_pos h]; exact (pair_points P h).choose_spec

namespace UnitArcDrawing
variable (A : UnitArcDrawing X)

theorem vertex_at (z : Plane) : z ∈ X ↔ ∃ v, A.D.vertex v = z := by
  change z ∈ (X : Set Plane) ↔ _
  rw [← A.vertex_set]; rfl

theorem not_vertex {e} {z : Plane} (hz : z ∈ A.D.interior e) : z ∉ X := by
  rintro h
  obtain ⟨v,hv⟩ := (A.vertex_at z).mp h
  obtain ⟨t,⟨h0,h1⟩,ht⟩ := hz
  exact A.D.avoids_vertices e t h0 h1 v (ht.trans hv.symm)

private theorem interior_or_vertex (e) {z : Plane} (hz : z ∈ Set.range (A.D.arc e)) :
    z ∈ A.D.interior e ∨ z ∈ X := by
  obtain ⟨t,rfl⟩ := hz
  by_cases h0 : t=0
  · exact Or.inr ((A.vertex_at _).2 ⟨_,(h0 ▸ A.D.at_zero e).symm⟩)
  by_cases h1 : t=1
  · exact Or.inr ((A.vertex_at _).2 ⟨_,(h1 ▸ A.D.at_one e).symm⟩)
  exact Or.inl ⟨t,⟨h0,h1⟩,rfl⟩

theorem finite_intersections : A.D.FiniteIntersections := by
  intro e f ne
  by_cases same : A.center e = A.center f
  · apply X.finite_toSet.subset
    rintro z ⟨a,b⟩
    rcases A.interior_or_vertex e a with ha|ha
    · rcases A.interior_or_vertex f b with hb|hb
      · exact (Set.disjoint_left.mp (A.same_center_disjoint ne same) ha hb).elim
      · exact hb
    · exact ha
  · have diff : (A.center e : Plane) ≠ A.center f := fun eq ↦ same (Subtype.ext eq)
    obtain ⟨T,_,spec⟩ := unit_intersections_le_two _ _ diff
    exact T.finite_toSet.subset fun z ⟨he,hf⟩ ↦ (spec z).2 ⟨A.on_circle _ _ he,A.on_circle _ _ hf⟩

theorem multiplicity_le_two (v w) : multiplicity A.G v w ≤ 2 := by
  classical
  by_cases eq : v=w
  · subst w
    have empty : (Finset.univ.filter fun e ↦ A.G.left e = v ∧ A.G.right e = v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro e he
      have h := (Finset.mem_filter.mp he).2
      exact (A.G.ordered e).ne (h.1.trans h.2.symm)
    simp [multiplicity,empty]
  obtain ⟨T,size,spec⟩ := unit_intersections_le_two _ _ (A.D.vertex_injective.ne eq)
  let S := Finset.univ.filter fun e ↦ A.G.left e = v ∧ A.G.right e = w
  change S.card ≤ 2
  apply le_trans (Finset.card_le_card_of_injOn (fun e ↦ (A.center e : Plane)) (t:=T) ?_ ?_) size
  · intro e he
    obtain ⟨hl,hr⟩ := (Finset.mem_filter.mp he).2
    apply (spec _).2
    have z := A.on_circle e _ ⟨0,rfl⟩
    have o := A.on_circle e _ ⟨1,rfl⟩
    rw [A.D.at_zero,hl,dist_comm] at z
    rw [A.D.at_one,hr,dist_comm] at o
    exact ⟨z,o⟩
  · intro e he f hf same
    have i := (Finset.mem_filter.mp he).2
    have j := (Finset.mem_filter.mp hf).2
    exact A.same_center_endpoint_inj (Subtype.ext same) (i.1.trans j.1.symm) (i.2.trans j.2.symm)

private abbrev Meeting := Σ _ : Finset Plane, Plane
private abbrev Mark := Σ _ : Plane, Finset Plane

private def centres (p : Crossing A.D) : Finset Plane :=
  {(A.center p.val.1 : Plane), (A.center p.val.2.1 : Plane)}

private theorem centre_ne (p : Crossing A.D) : (A.center p.val.1 : Plane) ≠ A.center p.val.2.1 := by
  intro eq
  exact Set.disjoint_left.mp (A.same_center_disjoint p.property.1.ne (Subtype.ext eq))
    p.property.2.1 p.property.2.2

private theorem event_id {e f} {z : Plane} (same : (A.center e : Plane) = A.center f)
    (he : z ∈ A.D.interior e) (hf : z ∈ A.D.interior f) : e = f := by
  by_contra ne
  exact Set.disjoint_left.mp (A.same_center_disjoint ne (Subtype.ext same)) he hf

private def crossingTo (p : Crossing A.D) : Meeting := ⟨A.centres p,p.val.2.2⟩

private theorem crossingTo_inj : Function.Injective A.crossingTo := by
  intro p q eq
  have cp := congrArg (fun t : Meeting ↦ t.1) eq
  have zz : p.val.2.2 = q.val.2.2 := congrArg (fun t : Meeting ↦ t.2) eq
  have mem1 : (A.center p.val.1 : Plane) ∈ A.centres q := by
    change A.centres p = A.centres q at cp
    rw [← cp]; simp [centres]
  have mem2 : (A.center p.val.2.1 : Plane) ∈ A.centres q := by
    change A.centres p = A.centres q at cp
    rw [← cp]; simp [centres]
  simp only [centres,Finset.mem_insert,Finset.mem_singleton] at mem1 mem2
  have h1 := p.property.2.1
  have h2 := p.property.2.2
  rw [zz] at h1 h2
  have i := p.property.1
  have j := q.property.1
  have lefts : p.val.1 = q.val.1 ∨ p.val.1 = q.val.2.1 :=
    mem1.imp (fun h ↦ A.event_id h h1 q.property.2.1) (fun h ↦ A.event_id h h1 q.property.2.2)
  have rights : p.val.2.1 = q.val.1 ∨ p.val.2.1 = q.val.2.1 :=
    mem2.imp (fun h ↦ A.event_id h h2 q.property.2.1) (fun h ↦ A.event_id h h2 q.property.2.2)
  apply Subtype.ext
  exact Prod.ext (by omega) (Prod.ext (by omega) zz)

private def markSet (X : Finset Plane) : Finset Mark :=
  X.sigma fun z ↦ (X.filter (fun v ↦ dist z v = 1)).powersetCard 2

private def allMeetings (X : Finset Plane) : Finset Meeting :=
  (X.powersetCard 2).sigma meeting

private theorem crossingTo_mem (p : Crossing A.D) : A.crossingTo p ∈ allMeetings X := by
  have h2 : (A.centres p).card = 2 := by simp [centres,A.centre_ne p]
  apply Finset.mem_sigma.mpr
  constructor
  · apply Finset.mem_powersetCard.mpr
    refine ⟨?_,h2⟩
    change A.centres p ⊆ X
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl|hr
    · exact (A.center p.val.1).property
    · obtain rfl := Finset.mem_singleton.mp hr
      exact (A.center p.val.2.1).property
  · apply ((meet_spec _ h2).2 _).2
    intro v hv
    rcases (Finset.mem_insert.mp hv) with rfl | right
    · exact A.on_circle _ _ (Set.image_subset_range _ _ p.property.2.1)
    · obtain rfl := Finset.mem_singleton.mp right
      exact A.on_circle _ _ (Set.image_subset_range _ _ p.property.2.2)

private theorem markTo_mem (p : Mark) (hp : p ∈ markSet X) : (⟨p.2,p.1⟩ : Meeting) ∈ allMeetings X := by
  obtain ⟨_,hs⟩ := Finset.mem_sigma.mp hp
  obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hs
  apply Finset.mem_sigma.mpr
  refine ⟨Finset.mem_powersetCard.mpr ⟨hsub.trans (Finset.filter_subset _ _),hcard⟩,?_⟩
  exact ((meet_spec _ hcard).2 _).2 (fun v hv ↦ (Finset.mem_filter.mp (hsub hv)).2)

private theorem allMeetings_card (X : Finset Plane) :
    (allMeetings X).card ≤ 2*X.card.choose 2 := by
  rw [allMeetings,Finset.card_sigma]
  calc
    _ ≤ ∑ _P ∈ X.powersetCard 2, 2 := Finset.sum_le_sum fun P h ↦ (meet_spec P (Finset.mem_powersetCard.mp h).2).1
    _ = _ := by simp [Finset.card_powersetCard,Nat.mul_comm]

/-- Distinct circle centres meet at most twice. Each crossing uses an unmarked point;
each original vertex reserves one meeting for every pair of its neighbouring centres. -/
theorem crossing_and_marked : A.D.crossingCount + ∑ x ∈ X, (unitDegree X x).choose 2 ≤
    2*X.card.choose 2 := by
  letI : Finite (Crossing A.D) := (finite_events A.D A.finite_intersections).to_subtype
  let f : Crossing A.D → ↥(allMeetings X) := fun p ↦ ⟨A.crossingTo p,A.crossingTo_mem p⟩
  let g : ↥(markSet X) → ↥(allMeetings X) := fun p ↦ ⟨⟨p.val.2,p.val.1⟩,markTo_mem _ p.property⟩
  have inj : Function.Injective (Sum.elim f g) := by
    apply Sum.elim_injective.mpr
    refine ⟨fun p q e ↦ A.crossingTo_inj (congrArg Subtype.val e),?_,?_⟩
    · rintro ⟨⟨x,V⟩,h⟩ ⟨⟨y,W⟩,h'⟩ eq
      have xy : x=y := congrArg (fun t : ↥(allMeetings X) ↦ t.val.2) eq
      have vw : V=W := congrArg (fun t : ↥(allMeetings X) ↦ t.val.1) eq
      subst y; subst W; rfl
    · intro p q eq
      have h : p.val.2.2 = q.val.1 := congrArg (fun t : ↥(allMeetings X) ↦ t.val.2) eq
      exact A.not_vertex p.property.2.1 (h ▸ (Finset.mem_sigma.mp q.property).1)
  have hc := Nat.card_le_card_of_injective _ inj
  have marked : (markSet X).card = ∑ x ∈ X, (unitDegree X x).choose 2 := by
    simp only [markSet,Finset.card_sigma,Finset.card_powersetCard,unitDegree]
  simp only [Nat.card_sum,card_crossing,Nat.card_eq_finsetCard,marked] at hc
  exact hc.trans (allMeetings_card X)

end UnitArcDrawing
end
end HadwigerNelson.Crossings

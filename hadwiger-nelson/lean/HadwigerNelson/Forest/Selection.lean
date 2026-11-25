import HadwigerNelson.Forest.Potential
import HadwigerNelson.Proof.PlacedEdges
import HadwigerNelson.Crossings.UnitDegrees

namespace HadwigerNelson.Forest
open Centres Placement MeasureTheory Set Crossings
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Choose one upward candidate for each blank head with a blank incoming tail. -/
theorem select_incoming {V : Type*} (B : Finset V) (rel : V → V → Prop) (h : V → ℝ) (d : V → ℕ)
    (grows : ∀ x ∈ B, ∀ y ∈ B, rel x y → h x < h y ∨ h x = h y ∧ d x < d y) :
    let H := B.filter (fun y => ∃ x ∈ B,rel x y)
    ∃ F : Finset (V × V), F.card = H.card ∧
      (∀ e ∈ F, e.1 ∈ B ∧ e.2 ∈ B ∧ rel e.1 e.2) ∧
      (∀ e ∈ F, ∀ f ∈ F, e.2=f.2 → e=f) ∧
      (B.Nonempty → F.card < B.card) := by
  classical
  intro H
  let tail y := if yes : ∃ x∈B,rel x y then yes.choose else y
  let edge (y : V) := (tail y,y)
  let F := H.image edge
  have valid (e) (he : e∈F) : e.1∈B ∧ e.2∈B ∧ rel e.1 e.2 := by
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hy,yes⟩ := Finset.mem_filter.mp hy
    have hi := yes.choose_spec
    simp only [edge,tail,dif_pos yes]
    exact ⟨hi.1,hy,hi.2⟩
  have distinct : Set.InjOn Prod.snd (F : Set (V×V)) := by
    rintro e he f hf eq
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hf
    exact congrArg edge eq
  refine ⟨F,Finset.card_image_of_injective _ (fun _ _ yes => congrArg Prod.snd yes),valid,
    fun _ he _ hf => distinct he hf,?_⟩
  intro hn
  have bound := incoming_forest h d F (fun e he => grows _ (valid e he).1 _ (valid e he).2.1 (valid e he).2.2)
    (fun _ he _ hf => distinct he hf) B (Finset.Subset.refl B) hn
  have unchanged : F.filter (fun z => z.1∈B ∧ z.2∈B) = F :=
    Finset.filter_true_of_mem (fun e he => ⟨(valid e he).1,(valid e he).2.1⟩)
  simpa only [unchanged] using bound

/-- One representative for each undirected unit edge, with the number of
representatives agreed with the half degree sum in the crossing bounds. -/
theorem unit_representatives (X : Finset Plane) :
    ∃ E : Finset (Plane×Plane), E.card=unitEdgeCount X ∧
      (∀ e∈E,e.1∈X ∧ e.2∈X ∧ dist e.1 e.2=1) ∧
      (∀ x∈X,∀ y∈X,dist x y=1 → (x,y)∈E ∨ (y,x)∈E) := by
  classical
  letI : LinearOrder Plane := linearOrderOfSTO WellOrderingRel
  let E := (X×ˢX).filter fun e => e.1<e.2 ∧ dist e.1 e.2=1
  have spec (x y : Plane) : (x,y)∈E ↔ (x∈X ∧ y∈X) ∧ x<y ∧ dist x y=1 := by simp [E]
  have sides (e) (he : e∈E) : e.1∈X ∧ e.2∈X ∧ dist e.1 e.2=1 := by
    have h := (spec e.1 e.2).mp he
    exact ⟨h.1.1,h.1.2,h.2.2⟩
  have cov (x) (hx : x∈X) (y) (hy : y∈X) (hu : dist x y=1) : (x,y)∈E ∨ (y,x)∈E := by
    rcases lt_trichotomy x y with lt | rfl | gt
    · exact Or.inl ((spec ..).mpr ⟨⟨hx,hy⟩,lt,hu⟩)
    · simp at hu
    · exact Or.inr ((spec ..).mpr ⟨⟨hy,hx⟩,gt,(dist_comm y x).trans hu⟩)
  let A := (X×ˢX).filter (fun e => dist e.1 e.2=1)
  have disj : Disjoint E (E.image Prod.swap) := by
    rw [Finset.disjoint_left]
    rintro ⟨x,y⟩ he hs
    obtain ⟨⟨u,v⟩,hu,e⟩ := Finset.mem_image.mp hs
    cases e
    exact ((spec ..).mp he).2.1.not_gt ((spec ..).mp hu).2.1
  have union : E∪E.image Prod.swap=A := by
    ext ⟨x,y⟩
    constructor
    · intro h
      rcases Finset.mem_union.mp h with he|hs
      · have z := sides _ he; exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨z.1,z.2.1⟩,z.2.2⟩
      · obtain ⟨⟨a,b⟩,he,e⟩ := Finset.mem_image.mp hs
        cases e
        have z := sides _ he
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨z.2.1,z.1⟩,(dist_comm ..).trans z.2.2⟩
    · intro h
      obtain ⟨xy,hu⟩ := Finset.mem_filter.mp h
      rcases cov x (Finset.mem_product.mp xy).1 y (Finset.mem_product.mp xy).2 hu with he|he
      · exact Finset.mem_union_left _ he
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(y,x),he,rfl⟩)
  have sum : A.card = ∑ x∈X,unitDegree X x := by
    simp only [A,unitDegree,Finset.card_filter,Finset.sum_product]
  have card := congrArg Finset.card union
  rw [Finset.card_union_of_disjoint disj,Finset.card_image_of_injective _ Prod.swap_injective,sum,sum_unitDegree] at card
  exact ⟨E,by omega,sides,cov⟩

end
end HadwigerNelson.Forest

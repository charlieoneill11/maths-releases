import HadwigerNelson.Centres.ArcLabels
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace HadwigerNelson.Centres
open Finset Crossings
noncomputable section
attribute [local instance] Classical.propDecidable

def linked (X : Finset Plane) (s t : Plane × Plane) : Prop :=
  t.1 ≠ t.2 ∧ consecutive X t.1 s.1 s.2 ∧ consecutive X t.2 s.1 s.2

def doubled (X : Finset Plane) (s : Plane × Plane) : Prop := ∃ t ∈ X ×ˢ X, linked X s t

theorem linked_chord {X s t} (h : linked X s t) : chord t.2 t.1 = dist s.1 s.2 :=
  chord_eq_dist h.1.symm h.2.1.1 h.2.2.2.1 h.2.2.2.2.1 h.2.1.2.1 h.2.1.2.2.1

theorem linked_swap_left {X s t} (h : linked X s t) : linked X s.swap t :=
  ⟨h.1,consecutive_comm.mp h.2.1,consecutive_comm.mp h.2.2⟩

theorem linked_swap_right {X s t} (h : linked X s t) : linked X s t.swap := ⟨h.1.symm,h.2.2,h.2.1⟩

private theorem ordered_options {α : Type*} {a b : α×α} (ne : a.1≠a.2)
    (fst : a.1=b.1 ∨ a.1=b.2) (snd : a.2=b.1 ∨ a.2=b.2) : a=b ∨ a=b.swap := by
  rcases fst with f|f <;> rcases snd with s|s
  · exact False.elim (ne (f.trans s.symm))
  · exact Or.inl (Prod.ext f s)
  · exact Or.inr (Prod.ext f s)
  · exact False.elim (ne (f.trans s.symm))

theorem linked_unique_right {X s t t'} (h : linked X s t) (k : linked X s t') : t'=t ∨ t'=t.swap := by
  have whereof {x} (c : consecutive X x s.1 s.2) : x=t.1 ∨ x=t.2 := common_pair h.2.1.1 h.1
    h.2.1.2.1 h.2.1.2.2.1 h.2.2.2.1 h.2.2.2.2.1 c.2.1 c.2.2.1
  exact ordered_options k.1 (whereof k.2.1) (whereof k.2.2)

theorem linked_unique_left {X s s' t} (h : linked X s t) (k : linked X s' t) : s'=s ∨ s'=s.swap := by
  have whereof {x} (u : dist t.1 x=1) (v : dist t.2 x=1) : x=s.1 ∨ x=s.2 := by
    apply common_pair h.1 h.2.1.1 <;> rw [dist_comm]
    · exact h.2.1.2.1
    · exact h.2.2.2.1
    · exact h.2.1.2.2.1
    · exact h.2.2.2.2.1
    · exact u
    · exact v
  exact ordered_options k.2.1.1 (whereof k.2.1.2.1 k.2.2.2.1) (whereof k.2.1.2.2.1 k.2.2.2.2.1)

private theorem count_fibre (X : Finset Plane) (P : Plane×Plane → Prop) [DecidablePred P]
    (sw : ∀ t, P t → P t.swap) (ne : ∀ t, P t → t.1 ≠ t.2)
    (un : ∀ t t', P t → P t' → t'=t ∨ t'=t.swap) :
    ((X×ˢX).filter P).card = if ∃ t∈X×ˢX, P t then 2 else 0 := by
  split
  next exist =>
    obtain ⟨t,ht,pt⟩ := exist
    have eq : (X×ˢX).filter P = {t,t.swap} := by
      ext a
      constructor
      · intro h; simpa only [mem_insert,mem_singleton] using un t a pt (mem_filter.mp h).2
      · intro ha; rcases mem_insert.mp ha with rfl|ha
        · exact mem_filter.mpr ⟨ht,pt⟩
        · obtain rfl := mem_singleton.mp ha
          exact mem_filter.mpr ⟨mem_product.mpr (mem_product.mp ht).symm,sw t pt⟩
    have diff : t ≠ t.swap := fun e ↦ ne t pt (congrArg Prod.fst e)
    simp [eq,diff]
  next no =>
    apply card_eq_zero.mpr; apply eq_empty_iff_forall_notMem.mpr; intro t h
    exact no ⟨t,(mem_filter.mp h).1,(mem_filter.mp h).2⟩

theorem doubled_iff (X : Finset Plane) (p q : Plane) :
    doubled X (p,q) ↔ ∃ u ∈ X, ∃ v ∈ X, u≠v ∧ consecutive X u p q ∧ consecutive X v p q := by
  constructor
  · rintro ⟨⟨u,v⟩,h,k⟩; exact ⟨u,(mem_product.mp h).1,v,(mem_product.mp h).2,k⟩
  · rintro ⟨u,hu,v,hv,k⟩; exact ⟨(u,v),mem_product.mpr ⟨hu,hv⟩,k⟩

theorem orientation_linked {X D : Finset Plane} (t : Plane × Plane) (hD : D ⊆ X)
    (ht : t ∈ X ×ˢ D) : orientation X D t.1 t.2 ↔ ∃ s ∈ X ×ˢ X, linked X s t := by
  obtain ⟨vX,uD⟩ := mem_product.mp ht
  constructor
  · rintro ⟨_,_,_,ne,p,hp,q,hq,cu,cv⟩
    exact ⟨(p,q),mem_product.mpr ⟨hp,hq⟩,ne.symm,cv,cu⟩
  · rintro ⟨⟨p,q⟩,pq,t'⟩
    exact ⟨vX,uD,hD uD,t'.1.symm,p,(mem_product.mp pq).1,q,(mem_product.mp pq).2,t'.2.2,t'.2.1⟩

/-- Exchange endpoints and centres in the relation of doubled unit-circle chords.
Each directed pair which occurs in a fibre has precisely two directed witnesses. -/
theorem orientation_count_all (X : Finset Plane) (r : ℝ) :
    (orientationSet X X r).card = ((X×ˢX).filter fun s ↦ doubled X s ∧ r ≤ dist s.1 s.2).card := by
  let G := X×ˢX
  let P (s t : Plane×Plane) := linked X s t ∧ r ≤ dist s.1 s.2
  have left (s) : (G.filter (P s)).card = if doubled X s ∧ r ≤ dist s.1 s.2 then 2 else 0 := by
    dsimp only [G]
    refine (show (G.filter (P s)).card = _ from count_fibre X (P s) (fun _ h ↦ ⟨linked_swap_right h.1,h.2⟩) (fun _ h ↦ h.1.1)
      (fun _ _ h k ↦ linked_unique_right h.1 k.1)).trans ?_
    congr 1
    exact propext ⟨fun ⟨t,ht,k⟩ ↦ ⟨⟨t,ht,k.1⟩,k.2⟩,fun ⟨⟨t,ht,k⟩,hr⟩ ↦ ⟨t,ht,k,hr⟩⟩
  have right (t) (ht : t∈G) : (G.filter fun s ↦ P s t).card =
      if orientation X X t.1 t.2 ∧ r ≤ chord t.2 t.1 then 2 else 0 := by
    dsimp only [G]
    refine (show (G.filter fun s ↦ P s t).card = _ from count_fibre X (fun s ↦ P s t) (fun s h ↦ ⟨linked_swap_left h.1,by change r ≤ dist s.2 s.1; rw [dist_comm]; exact h.2⟩)
      (fun _ h ↦ h.1.2.1.1) (fun _ _ h k ↦ linked_unique_left h.1 k.1)).trans ?_
    congr 1
    rw [orientation_linked t (fun _ h ↦ h) ht]
    exact propext ⟨fun ⟨s,hs,k⟩ ↦ ⟨⟨s,hs,k.1⟩,(linked_chord k.1).symm ▸ k.2⟩,
      fun ⟨⟨s,hs,k⟩,hr⟩ ↦ ⟨s,hs,k,linked_chord k ▸ hr⟩⟩
  have count := sum_filter_card G G P
  have lc : (∑ s ∈ G, (G.filter (P s)).card) = 2*((X×ˢX).filter fun s ↦ doubled X s ∧ r ≤ dist s.1 s.2).card := by
    simp_rw [left]; rw [Finset.card_filter,Finset.mul_sum]
    exact sum_congr rfl fun s _ ↦ by split <;> simp_all
  have rc : (∑ t ∈ G, (G.filter fun s ↦ P s t).card) = 2*(orientationSet X X r).card := by
    unfold orientationSet
    rw [Finset.card_filter,Finset.mul_sum]
    apply sum_congr rfl; intro t ht; rw [right t ht]; split <;> simp_all
  omega

end
end HadwigerNelson.Centres

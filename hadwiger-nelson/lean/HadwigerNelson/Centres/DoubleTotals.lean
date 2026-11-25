import HadwigerNelson.Centres.ArcAssignment

namespace HadwigerNelson.Centres
open Finset Crossings
noncomputable section
attribute [local instance] Classical.propDecidable

theorem even_symmetric_count (X : Finset Plane) (P : Plane × Plane → Prop) [DecidablePred P]
    (sym : ∀ p q, P (p,q) ↔ P (q,p)) (ne : ∀ p, ¬P (p,p)) :
    Even ((X×ˢX).filter P).card := by
  let f (p q : Plane) : ℕ := if P (p,q) then 1 else 0
  have fcomm (p q : Plane) : f p q = f q p := by simp only [f,sym p q]
  have even : Even (∑ p ∈ X, ∑ q ∈ X, f p q) := by
    induction X using Finset.induction_on with
    | empty => simp
    | @insert p X hp ih =>
      obtain ⟨k,hk⟩ := ih
      refine ⟨k+∑ q ∈ X, f p q,?_⟩
      rw [Finset.sum_insert hp]
      simp_rw [Finset.sum_insert hp,Finset.sum_add_distrib]
      rw [hk,show f p p=0 by simp [f,ne]]
      rw [Finset.sum_congr (s₁:=X) rfl fun q _ ↦ fcomm q p]
      simp only [Nat.zero_add]
      ac_rfl
  simpa only [Finset.card_filter,Finset.sum_product,f] using even

theorem doubled_comm (X : Finset Plane) (p q : Plane) : doubled X (p,q) ↔ doubled X (q,p) :=
  ⟨fun ⟨t,ht,k⟩ ↦ ⟨t,ht,linked_swap_left k⟩,fun ⟨t,ht,k⟩ ↦ ⟨t,ht,linked_swap_left k⟩⟩

theorem doubled_ne {X : Finset Plane} {p q} (h : doubled X (p,q)) : p ≠ q := by
  obtain ⟨_,_,k⟩ := h; exact k.2.1.1

theorem all_doubles_card (X : Finset Plane) : ((X×ˢX).filter (doubled X)).card = 2*doubledPairs X := by
  let U := (X×ˢX).filter (doubled X)
  obtain ⟨k,hk⟩ := even_symmetric_count X (doubled X) (doubled_comm X) (fun _ h ↦ doubled_ne h rfl)
  have eq : doubledPairs X = U.card/2 := by
    simp only [doubledPairs,U,Finset.card_filter,Finset.sum_product,doubled_iff]
  rw [eq]
  change U.card=k+k at hk; change U.card=2*(U.card/2); omega

theorem small_doubles_card (X : Finset Plane) (r : ℝ) :
    ((X×ˢX).filter fun s ↦ doubled X s ∧ dist s.1 s.2<r).card = 2*shortDoubledCount X r := by
  let P := fun (s : Plane × Plane) ↦ doubled X s ∧ dist s.1 s.2<r
  obtain ⟨k,hk⟩ := even_symmetric_count X P (by intro p q; simp only [P,doubled_comm X p q,dist_comm p q])
    (fun _ h ↦ doubled_ne h.1 rfl)
  let U := (X×ˢX).filter P
  have eq : shortDoubledCount X r = U.card/2 := by
    simp only [shortDoubledCount,U,P,Finset.card_filter,Finset.sum_product,doubled_iff,and_comm]
  rw [eq]
  change U.card=k+k at hk; change U.card=2*(U.card/2); omega

theorem orientation_split (X : Finset Plane) (r : ℝ) :
    (orientationSet X X r).card + 2*shortDoubledCount X r = 2*doubledPairs X := by
  rw [orientation_count_all,←small_doubles_card,←all_doubles_card]
  let ALL := (X×ˢX).filter (doubled X)
  have split := ALL.card_filter_add_card_filter_not (fun s ↦ r ≤ dist s.1 s.2)
  simpa only [ALL,Finset.filter_filter,not_le] using split

theorem many_orientations (X D : Finset Plane) (r b : ℝ) (hb : admissible X r b)
    (hd : minNonisolatedDegree X 3) :
    (doubledPairs X:ℝ)-b-(outsideDegree X D:ℝ)/2 ≤ (orientationSet X D r).card/2 := by
  have omitted := omitted_heads X D r hd
  have split := orientation_split X r
  have a : ((orientationSet X X r).card:ℝ) + 2*(shortDoubledCount X r:ℝ)=2*doubledPairs X := by exact_mod_cast split
  have bnd : ((orientationSet X X r).card:ℝ) ≤ (orientationSet X D r).card + (outsideDegree X D:ℝ) := by exact_mod_cast omitted
  linarith [hb.2.1]

theorem paired_le_twice (X : Finset Plane) (hd : minNonisolatedDegree X 3) : (pairedArcs X).card ≤ 2*doubledPairs X := by
  have h := card_paired_le X hd
  have hn := orientation_split X 0
  omega

end
end HadwigerNelson.Centres

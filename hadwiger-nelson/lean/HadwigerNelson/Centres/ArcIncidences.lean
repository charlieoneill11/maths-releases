import HadwigerNelson.Centres.ArcAssignment
import HadwigerNelson.Centres.ArcCounts

namespace HadwigerNelson.Centres
open Finset Crossings
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Directed endpoint labels for each of the two orientations of an arc. -/
def ends {X : Finset Plane} (e : Arc X) (rev : Bool) : Plane×Plane :=
  if rev then (finish e,start e) else (start e,finish e)

theorem ends_consecutive {X : Finset Plane} (hd : minNonisolatedDegree X 3) (e : Arc X) (b : Bool) :
    consecutive X (head e) (ends e b).1 (ends e b).2 := by
  cases b
  · exact arc_consecutive hd e
  · exact consecutive_comm.mp (arc_consecutive hd e)

theorem ends_dist {X : Finset Plane} (e : Arc X) (b : Bool) :
    dist (ends e b).1 (ends e b).2 = dist (start e) (finish e) := by
  cases b <;> simp [ends,dist_comm (finish e) (start e)]

theorem ends_mem {X : Finset Plane} (e : Arc X) (b : Bool) :
    (ends e b).1∈X ∧ (ends e b).2∈X := by
  cases b
  · exact ⟨start_mem e,finish_mem e⟩
  · exact ⟨finish_mem e,start_mem e⟩

theorem ends_injective {X : Finset Plane} (hd : minNonisolatedDegree X 3)
    {e f : Arc X} {a b : Bool} (h : ends e a=ends f b) (c : (head e:Plane)=head f) : e=f ∧ a=b := by
  have u := congrArg Prod.fst h
  have v := congrArg Prod.snd h
  have eq : e=f := by
    apply arc_ext hd c
    cases a <;> cases b <;> first
      | exact Or.inl ⟨u,v⟩
      | exact Or.inl ⟨v,u⟩
      | exact Or.inr ⟨u,v⟩
      | exact Or.inr ⟨v,u⟩
  subst f
  refine ⟨rfl,?_⟩
  cases a <;> cases b <;> first
    | rfl
    | exact False.elim ((arc_consecutive hd e).1 u)
    | exact False.elim ((arc_consecutive hd e).1 v)

theorem ends_single_injective {X : Finset Plane} (hd : minNonisolatedDegree X 3)
    {e f : Arc X} {a b : Bool} (single : ¬paired e) (h : ends e a=ends f b) : e=f ∧ a=b := by
  apply ends_injective hd h
  by_contra ne
  have cf := ends_consecutive hd f b
  rw [←h] at cf
  apply single
  refine ⟨head f,(head f).property,Ne.symm ne,?_⟩
  cases a
  · exact cf
  · exact consecutive_comm.mp cf

private def records (X A B : Finset Plane) (r : ℝ) : Finset ((Plane×Plane)×Plane) :=
  ((A×ˢB)×ˢX).filter fun v ↦ consecutive X v.2 v.1.1 v.1.2 ∧ dist v.1.1 v.1.2<r

private theorem records_card (X A B : Finset Plane) (r : ℝ) : (records X A B r).card=arcCount X r A B := by
  simp only [records,arcCount,circleCarriers,Finset.card_filter,Finset.sum_product]

private theorem record_inj {X : Finset Plane} (hd : minNonisolatedDegree X 3) :
    Function.Injective (fun v : Arc X × Bool ↦ (ends v.1 v.2,(head v.1:Plane))) := by
  intro a b h
  obtain ⟨u,v⟩ := ends_injective hd (congrArg Prod.fst h) (congrArg Prod.snd h)
  exact Prod.ext u v

theorem card_short_arcs_le (X : Finset Plane) (hd : minNonisolatedDegree X 3) (r : ℝ) :
    ((univ : Finset (Arc X)).filter fun e ↦ dist (start e) (finish e)<r).card ≤ shortArcCount X r := by
  let S := (univ : Finset (Arc X)).filter fun e ↦ dist (start e) (finish e)<r
  have bound : (S×ˢ(univ : Finset Bool)).card ≤ (records X X X r).card := by
    apply card_le_card_of_injOn (fun v ↦ (ends v.1 v.2,(head v.1:Plane))) _ (fun _ _ _ _ eq ↦ record_inj hd eq)
    intro v hv
    have short := (mem_filter.mp (mem_product.mp hv).1).2
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_product.mpr (ends_mem ..),(head v.1).property⟩,
      ends_consecutive hd _ _,(ends_dist ..).symm ▸ short⟩
  simp only [card_product,card_univ,Fintype.card_bool,records_card] at bound
  rw [shortArcCount_eq]
  change S.card≤_
  omega

theorem card_touched_le (X U : Finset Plane) (hd : minNonisolatedDegree X 3) (sub : U ⊆ X) :
    ((univ : Finset (Arc X)).filter fun e ↦ start e∈U ∨ finish e∈U).card ≤ 2*∑ p∈U, unitDegree X p := by
  let S := (univ : Finset (Arc X)).filter fun e ↦ start e∈U ∨ finish e∈U
  let b (e : Arc X) := decide (start e∉U)
  have bound : S.card ≤ (records X U X 3).card := by
    apply card_le_card_of_injOn (fun e ↦ (ends e (b e),(head e:Plane)))
    · intro e he
      have touch := (mem_filter.mp he).2
      have yes : (ends e (b e)).1∈U := by
        by_cases a : start e∈U
        · simpa [b,ends,a] using a
        · simpa [b,ends,a] using touch.resolve_left a
      have seg := ends_consecutive hd e (b e)
      have bounded := dist_triangle_left (ends e (b e)).1 (ends e (b e)).2 (head e:Plane)
      rw [seg.2.1,seg.2.2.1] at bounded
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_product.mpr ⟨yes,(ends_mem ..).2⟩,(head e).property⟩,seg,by linarith⟩
    · intro a _ c _ h; exact (ends_injective hd (congrArg Prod.fst h) (congrArg Prod.snd h)).1
  rw [records_card] at bound
  exact bound.trans (arcCount_endpoint X U 3 sub)

end
end HadwigerNelson.Centres

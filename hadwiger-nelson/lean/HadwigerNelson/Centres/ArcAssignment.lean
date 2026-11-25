import HadwigerNelson.Centres.ArcTotals
import HadwigerNelson.Centres.OrientationCounts

namespace HadwigerNelson.Centres
open Finset Crossings
noncomputable section
attribute [local instance] Classical.propDecidable

theorem arc_ext {X : Finset Plane} (hd : minNonisolatedDegree X 3) {e f : Arc X}
    (c : (head e:Plane) = head f) (p : (start e=start f ∧ finish e=finish f) ∨
      (start e=finish f ∧ finish e=start f)) : e=f := by
  obtain ⟨x,i⟩ := e; obtain ⟨y,j⟩ := f
  have xy : x=y := Subtype.ext c
  subst y
  exact congrArg (Sigma.mk x) (index_eq hd i j p)

def assigned {X D : Finset Plane} {v u : Plane} (h : orientation X D v u) : Arc X :=
  Classical.choose (arc_for_orientation h)

theorem assigned_spec {X D : Finset Plane} {v u : Plane} (h : orientation X D v u) :
    (head (assigned h):Plane)=u ∧ v≠u ∧ consecutive X v (start (assigned h)) (finish (assigned h)) :=
  Classical.choose_spec (arc_for_orientation h)

theorem assigned_inj {X D : Finset Plane} (hd : minNonisolatedDegree X 3)
    {t t' : Plane×Plane} (a : orientation X D t.1 t.2) (b : orientation X D t'.1 t'.2)
    (eq : assigned a=assigned b) : t=t' := by
  obtain ⟨h1,ne,ac⟩ := assigned_spec a
  obtain ⟨h2,ne',bc⟩ := assigned_spec b
  rw [←eq] at h2 bc
  have second := h1.symm.trans h2
  exact Prod.ext (partner_unique (by rwa [h1]) (by rwa [h2]) (arc_consecutive hd _) ac bc) second

theorem assigned_paired {X D : Finset Plane} {v u : Plane} (h : orientation X D v u) : paired (assigned h) := by
  obtain ⟨a,ne,b⟩ := assigned_spec h
  exact ⟨v,h.1,by rwa [a],b⟩

theorem assigned_length {X D : Finset Plane} (hd : minNonisolatedDegree X 3) {v u : Plane} (h : orientation X D v u) :
    arcLength X u v ≤ length (assigned h) := by
  obtain ⟨a,ne,b⟩ := assigned_spec h
  have aux := oriented_length_le hd _ (v:=v) (by rw [a]; exact ne.symm) b
  rwa [a] at aux

theorem assigned_chord {X D : Finset Plane} (hd : minNonisolatedDegree X 3) {v u : Plane} (h : orientation X D v u) :
    chord u v = dist (start (assigned h)) (finish (assigned h)) := by
  obtain ⟨a,ne,b⟩ := assigned_spec h
  have c := arc_consecutive hd (assigned h)
  rw [a] at c
  exact chord_eq_dist ne.symm c.1 c.2.1 c.2.2.1 b.2.1 b.2.2.1

def pairedArcs (X : Finset Plane) : Finset (Arc X) := univ.filter paired

theorem card_paired_le (X : Finset Plane) (hd : minNonisolatedDegree X 3) :
    (pairedArcs X).card ≤ (orientationSet X X 0).card := by
  let partner (e : ↥(pairedArcs X)) := Classical.choose ((mem_filter.mp e.property).2)
  have spec (e : ↥(pairedArcs X)) : partner e∈X ∧ partner e≠head e.val ∧
      consecutive X (partner e) (start e.val) (finish e.val) := Classical.choose_spec ((mem_filter.mp e.property).2)
  let label (e : ↥(pairedArcs X)) := (partner e,(head e.val:Plane))
  have rel (e : ↥(pairedArcs X)) : linked X (start e.val,finish e.val) (label e) :=
    ⟨(spec e).2.1,(spec e).2.2,arc_consecutive hd _⟩
  let T := orientationSet X X 0
  let f (e : ↥(pairedArcs X)) : T := ⟨label e,mem_filter.mpr ⟨mem_product.mpr ⟨(spec e).1,(head e.val).property⟩,
    (orientation_linked _ (fun _ a ↦ a) (mem_product.mpr ⟨(spec e).1,(head e.val).property⟩)).mpr
      ⟨(start e.val,finish e.val),mem_product.mpr ⟨start_mem _,finish_mem _⟩,rel e⟩,Real.sqrt_nonneg _⟩⟩
  have inj : Function.Injective f := by
    intro e g same
    have pair : label e=label g := congrArg Subtype.val same
    have cr := rel e
    rw [pair] at cr
    have ends := linked_unique_left (rel g) cr
    apply Subtype.ext
    apply arc_ext hd (congrArg Prod.snd pair)
    rcases ends with eq|eq <;> exact (by first | exact Or.inl ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩ |
      exact Or.inr ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩)
  simpa [T] using Fintype.card_le_of_injective f inj

theorem omitted_heads (X D : Finset Plane) (r : ℝ) (hd : minNonisolatedDegree X 3) :
    (orientationSet X X r).card ≤ (orientationSet X D r).card + outsideDegree X D := by
  let S := orientationSet X X r
  let good := S.filter fun p ↦ p.2∈D
  let bad := S.filter fun p ↦ p.2∉D
  have sub : good ⊆ orientationSet X D r := by
    intro p h; obtain ⟨yes,d⟩ := mem_filter.mp h
    obtain ⟨px,⟨vX,_,uX,more⟩,hr⟩ := mem_filter.mp yes
    exact mem_filter.mpr ⟨mem_product.mpr ⟨vX,d⟩,⟨vX,d,uX,more⟩,hr⟩
  have get (p : ↥bad) : orientation X X p.val.1 p.val.2 := (mem_filter.mp (mem_filter.mp p.property).1).2.1
  let T := arcsOn X (X\D)
  let f (p : ↥bad) : T := ⟨assigned (get p),mem_arcsOn.mpr (by rw [(assigned_spec (get p)).1]; exact mem_sdiff.mpr ⟨(get p).2.2.1,(mem_filter.mp p.property).2⟩)⟩
  have inj : Function.Injective f := fun p q h ↦ Subtype.ext (assigned_inj hd (get p) (get q) (congrArg Subtype.val h))
  have count : bad.card≤outsideDegree X D := by
    simpa only [Fintype.card_coe,T,card_arcsOn X _ sdiff_subset,outsideDegree] using Fintype.card_le_of_injective f inj
  have split : good.card+bad.card=S.card := card_filter_add_card_filter_not ..
  have yes := card_le_card sub
  change S.card ≤ _
  omega

end
end HadwigerNelson.Centres

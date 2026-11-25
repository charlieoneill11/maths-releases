import SevenCycle.Blueprint.Definitions
import SevenCycle.Proof.Bands

/-! Geometry of the marked projections with their axes kept in ambient coordinates. -/

namespace SevenCycle.Proof.FrameGeometry

open Blueprint Blueprint.SearchSpec

theorem mem_face {C : Points} {k : Axis} {p : Height → Prop} [DecidablePred p]
    {y : Tuple 4} : y ∈ face C k p ↔ ∃ x ∈ C, p (x k) ∧ setHeight x k 0 = y := by
  simp [face, and_assoc]

private theorem face_swap_subset (C : Points) {k l : Axis} (hkl : k ≠ l)
    (p q : Height → Prop) [DecidablePred p] [DecidablePred q] :
    face (face C k p) l q ⊆ face (face C l q) k p := by
  intro z hz
  obtain ⟨y, hy, hq, rfl⟩ := mem_face.mp hz
  obtain ⟨x, hx, hp, rfl⟩ := mem_face.mp hy
  refine mem_face.mpr ⟨setHeight x l 0, mem_face.mpr ⟨x, hx, ?_, rfl⟩, ?_, ?_⟩
  · simpa [setHeight, Function.update_of_ne hkl.symm] using hq
  · simpa [setHeight, Function.update_of_ne hkl] using hp
  · exact (Function.update_comm hkl 0 0 x).symm

theorem face_comm (C : Points) {k l : Axis} (hkl : k ≠ l)
    (p q : Height → Prop) [DecidablePred p] [DecidablePred q] :
    face (face C k p) l q = face (face C l q) k p :=
  Finset.Subset.antisymm (face_swap_subset C hkl p q) (face_swap_subset C hkl.symm q p)

theorem stripe_comm (C : Points) {k l : Axis} (hkl : k ≠ l) (s t : Height) :
    stripe (stripe C k s) l t = stripe (stripe C l t) k s :=
  face_comm C hkl (fun z => z = s ∨ z = s + 1) (fun z => z = t ∨ z = t + 1)

theorem drop_setHeight (k : Axis) (x : Tuple 4) (h : Height) :
    dropCoord k (setHeight x k h) = dropCoord k x := by
  funext j
  simp [dropCoord, setHeight]

theorem stripe_injective {C : Points} (hc : packing cycleStep C) (k : Axis) (t : Height) :
    Set.InjOn (fun x => setHeight x k 0) (band C k t : Set (Tuple 4)) := by
  intro x hx y hy he
  apply (Bands.band_projection hc k t).1 hx hy
  simpa only [drop_setHeight] using congrArg (dropCoord k) he

theorem stripe_packing {C : Points} (hc : packing cycleStep C) (k : Axis) (t : Height) :
    packing cycleStep (stripe C k t) := by
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hinj, hproj⟩ := Bands.band_projection hc k t
  apply hproj (dropCoord k a) (Finset.mem_image_of_mem _ ha)
    (dropCoord k b) (Finset.mem_image_of_mem _ hb)
  constructor
  · exact fun h => hxy.1 (congrArg (fun w => setHeight w k 0) (hinj ha hb h))
  · intro j
    simpa [dropCoord, setHeight, Function.update_of_ne (k.succAbove_ne j)] using hxy.2 (k.succAbove j)

theorem face33 {C : Points} (hc : packing cycleStep C) {k : Axis} {t : Height}
    (ht : t ∈ fullStarts C k) : Face33 k (stripe C k t) := by
  refine ⟨?_, stripe_packing hc k t, ?_⟩
  · exact (Finset.card_image_of_injOn (stripe_injective hc k t)).trans (Finset.mem_filter.mp ht).2
  · intro y hy
    obtain ⟨x, _, _, rfl⟩ := mem_face.mp hy
    simp [setHeight]

theorem contacts {C : Points} {m : Frame} (hc : packing cycleStep C) (hm : Marked m C)
    (k : Axis) : Contacts m k (projections m C k false) (projections m C k true) := by
  intro l hl b
  exact ⟨projections m C l b, face33 (k := l) (t := start m l b) hc (hm.2.1 l b),
    stripe_comm C hl.symm _ _, stripe_comm C hl.symm _ _⟩

theorem projected_join {C : Points} {m : Frame} (hc : packing cycleStep C) (hm : Marked m C)
    (k : Axis) : joined m k (projections m C k false) (projections m C k true) (projections m C) := by
  constructor
  · intro l hl b
    exact ⟨face33 (k := l) (t := start m l b) hc (hm.2.1 l b), stripe_comm C hl.symm _ _, stripe_comm C hl.symm _ _⟩
  · intro i j _ _ hij b c
    exact stripe_comm C hij _ _

theorem plane_union (C : Points) (k : Axis) (i : Height) :
    plane C k i ∪ plane C k (i+1) = stripe C k i := by
  simp [plane, stripe, face, Finset.filter_or, Finset.image_union]

theorem planes_disjoint {C : Points} (hc : packing cycleStep C) (k : Axis) (i : Height) :
    Disjoint (plane C k i) (plane C k (i+1)) := by
  refine Finset.disjoint_left.mpr fun ⦃u⦄ hu hv => ?_
  obtain ⟨x, hx, hxk, rfl⟩ := mem_face.mp hu
  obtain ⟨y, hy, hyk, hyx⟩ := mem_face.mp hv
  have eq := stripe_injective hc k i (Finset.mem_filter.mpr ⟨hy, Or.inr hyk⟩)
    (Finset.mem_filter.mpr ⟨hx, Or.inl hxk⟩) hyx
  subst y
  have : (1 : Height) = 0 := add_left_cancel (show i+1 = i+0 by rw [← hyk, hxk, add_zero])
  exact (by decide : (1 : Height) ≠ 0) this

end SevenCycle.Proof.FrameGeometry

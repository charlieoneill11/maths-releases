import SevenCycleRuntime.Contacts
import SevenCycle.TypeThree.Coverage
import SevenCycle.Bitsets.Orbit
import SevenCycle.Proof.Bands
import Std.Data.HashMap.Lemmas
import SevenCycle.TypeThree.FastCuts

namespace SevenCycle.Adjacent.Contacts

open Proof Blueprint Bitsets

private theorem insert_iff (tbl : Index) (w : Cube) (k : Key) (p : Plane) :
    p ∈ (insert tbl w).getD k #[] ↔
      p ∈ tbl.getD k #[] ∨ key w = k ∧ p = middle w := by
  by_cases hk : key w = k
  · subst k
    simp only [insert, Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getElem?_alter,
      beq_self_eq_true, if_true, Option.getD_some, true_and]
    split
    · next h => exact ⟨Or.inl, fun e => e.elim id (fun eq => eq ▸ Array.contains_iff_mem.mp h)⟩
    · exact Array.mem_push
  · simp [insert, Std.HashMap.getD_alter, hk]

private theorem orbit_contains (images : Array Cube) (tbl : Index) (w : Cube)
    (h : middle w ∈ tbl.getD (key w) #[] ∨ w ∈ images) :
    middle w ∈ (images.foldl insert tbl).getD (key w) #[] := by
  rw [← Array.foldl_toList]
  have aux (xs : List Cube) (t : Index)
      (hx : middle w ∈ t.getD (key w) #[] ∨ w ∈ xs) :
      middle w ∈ (xs.foldl insert t).getD (key w) #[] := by
    induction xs generalizing t with
    | nil => simpa using hx
    | cons a xs ih =>
      apply ih
      rcases hx with h | h
      · exact Or.inl ((insert_iff ..).mpr (Or.inl h))
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl ((insert_iff ..).mpr (Or.inr ⟨rfl, rfl⟩))
        · exact Or.inr h
  exact aux _ _ (h.imp_right Array.mem_toList_iff.mpr)

theorem index_covers (rows : Array Cube) {r w : Cube} (hr : r ∈ rows)
    (hw : w ∈ orbitImages r) : middle w ∈ (index orbitImages rows).getD (key w) #[] := by
  let has (m : Index) := middle w ∈ m.getD (key w) #[]
  let put (m : Index) (a : Cube) := (orbitImages a).foldl insert m
  have aux (xs : List Cube) (m : Index) (h : has m ∨ r ∈ xs) : has (xs.foldl put m) := by
    induction xs generalizing m with
    | nil => simpa using h
    | cons a xs ih =>
      apply ih
      rcases h with h | h
      · exact Or.inl (orbit_contains _ m w (.inl h))
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl (orbit_contains _ m w (.inr hw))
        · exact Or.inr h
  unfold index
  rw [← Array.foldl_toList]
  exact aux _ _ (.inr (Array.mem_toList_iff.mpr hr))

theorem crossing {C : SearchSpec.Points} (a : Fin 3) {j h : Height} {s w : Cube}
    (hs : TypeThree.RepresentsBand C 0 h s) (hw : TypeThree.RepresentsBand C a.succ j w) :
    Bitsets.cut s a j = Bitsets.cut w 0 h := by
  apply TypeThree.equal_cuts (i := a) (j := 0) _ _ _ hs hw
  · simp
  · exact (by decide : ∀ i : Fin 3, i.succ.succAbove 0 = 0) a
  · exact (by decide : ∀ (a : Fin 3) (i : Fin 2),
      (0 : Fin 4).succAbove (a.succAbove i) = a.succ.succAbove ((0 : Fin 3).succAbove i)) a

abbrev AtlasComplete :=
  ∀ D : Finset (Tuple 3), packing cycleStep D → D.card = 33 →
    ∃ q : Fin atlasPlanes.size, ∃ g : Blueprint.Isometry 3, D = actOnCode g (atlasRepresentative q)

/-- One contact in an actual packing selects a middle entry, including its
orientation, from the table of all marked atlas images. -/
theorem contact_covers (atlas : AtlasComplete)
    {C : SearchSpec.Points} (hc : packing cycleStep C) {s t : Cube}
    (hs : TypeThree.RepresentsBand C 0 0 s) (ht : TypeThree.RepresentsBand C 0 1 t)
    {a : Fin 3} {j : Height} (hj : j ∈ fullStarts C a.succ) :
    ∃ w : Cube, TypeThree.RepresentsBand C a.succ j w ∧
      middle w ∈ (index orbitImages atlasPlanes).getD (anchorKey s t a j) #[] := by
  obtain ⟨hinj, hcode⟩ := Bands.band_projection hc a.succ j
  have hsize : (projectedBand C a.succ j).card = 33 :=
    (Finset.card_image_of_injOn hinj).trans (Finset.mem_filter.mp hj).2
  obtain ⟨q, g, h⟩ := atlas _ hcode hsize
  obtain ⟨w, hw, he⟩ := orbitImages_complete g atlasPlanes[q]
  have hr : TypeThree.RepresentsBand C a.succ j w := he.trans h.symm
  refine ⟨w, hr, ?_⟩
  have hkey : key w = anchorKey s t a j := by
    change (TypeThree.fastCut w 0 0, TypeThree.fastCut w 0 1) = _
    simp only [anchorKey, TypeThree.fastCut_eq, crossing a hs hr,
      crossing a ht hr]
    rfl
  rw [← hkey]
  exact index_covers _ (Array.getElem_mem q.isLt) hw

private theorem contains_of_entry {t : Index} {k : Key} {p : Plane} (h : p ∈ t.getD k #[]) :
    t.contains k = true := by
  by_contra hh
  have hm : k ∉ t := fun hmem => hh (Std.HashMap.contains_iff_mem.mpr hmem)
  simp [Std.HashMap.getD_eq_fallback hm] at h

theorem centers_mem {idx : Index} {s t : Cube} {a : Fin 3} {gap c : Height}
    (h0 : idx.contains (anchorKey s t a c) = true)
    (h1 : idx.contains (anchorKey s t a (c-gap)) = true) : c ∈ centers idx s t a gap := by
  apply Array.mem_filter.mpr
  refine ⟨Array.mem_ofFn.mpr ⟨c, rfl⟩, ?_⟩
  have get (f : Fin 7 → Bool) (i : Fin 7) : (Vector.ofFn f).get i = f i := by
    change (Vector.ofFn f)[i.val] = f i
    rw [Vector.getElem_ofFn]
  simp only [get, h0, h1, Bool.and_self]

theorem checkContacts_sound (atlas : AtlasComplete)
    {C : SearchSpec.Points} (hc : packing cycleStep C) {s t : Cube}
    (hs : TypeThree.RepresentsBand C 0 0 s) (ht : TypeThree.RepresentsBand C 0 1 t)
    (gaps cs : Vector Height 3)
    (full : ∀ a : Fin 3, cs.get a ∈ fullStarts C a.succ ∧ cs.get a - gaps.get a ∈ fullStarts C a.succ)
    {next : Height → Height → Height → Bool}
    (ok : checkContacts (index orbitImages atlasPlanes) s t gaps next = true) :
    next (cs.get 0) (cs.get 1) (cs.get 2) = true := by
  have mem (a : Fin 3) : cs.get a ∈ centers (index orbitImages atlasPlanes) s t a (gaps.get a) := by
    apply centers_mem
    · obtain ⟨w, _, h⟩ := contact_covers atlas hc hs ht (full a).1
      exact contains_of_entry h
    · obtain ⟨w, _, h⟩ := contact_covers atlas hc hs ht (full a).2
      exact contains_of_entry h
  have notEmpty (a : Fin 3) : (centers (index orbitImages atlasPlanes) s t a (gaps.get a)).isEmpty = false :=
    Array.isEmpty_eq_false_iff_exists_mem.mpr ⟨_, mem a⟩
  simp only [checkContacts, notEmpty, Bool.false_or] at ok
  exact Array.all_eq_true'.mp (Array.all_eq_true'.mp (Array.all_eq_true'.mp ok _ (mem 0)) _ (mem 1)) _ (mem 2)

end SevenCycle.Adjacent.Contacts

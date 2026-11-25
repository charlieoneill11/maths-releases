import SevenCycleRuntime.AdjacentDomains
import SevenCycle.Adjacent.BandJoin
import SevenCycle.Adjacent.MiddleWindow

namespace SevenCycle.Adjacent.BandJoin
open Bitsets Proof Blueprint

private theorem mem_insertIf (needed : Prefix → Bool) (m : Index) (w r : Cube) (k : Prefix) :
    r ∈ (insertIf needed m w).getD k #[] ↔ r ∈ m.getD k #[] ∨
      needed k = true ∧ prefixOf w = k ∧ r = w := by
  by_cases key : prefixOf w = k
  · subst k
    by_cases hn : needed (prefixOf w) = true <;>
      simp [insertIf, hn, Std.HashMap.getD_eq_getD_getElem?]
  · by_cases h : needed (prefixOf w) = true <;> simp [insertIf, h, key, Std.HashMap.getD_alter]

private theorem orbit_add (needed : Prefix → Bool) (rows : Array Cube) (m : Index) (r : Cube)
    (hn : needed (prefixOf r) = true)
    (h : r ∈ m.getD (prefixOf r) #[] ∨ r ∈ rows) :
    r ∈ (rows.foldl (insertIf needed) m).getD (prefixOf r) #[] := by
  rw [← Array.foldl_toList]
  have aux (xs : List Cube) (t : Index) (hx : r ∈ t.getD (prefixOf r) #[] ∨ r ∈ xs) :
      r ∈ (xs.foldl (insertIf needed) t).getD (prefixOf r) #[] := by
    induction xs generalizing t with
    | nil => simpa using hx
    | cons a xs ih =>
      apply ih
      rcases hx with h | h
      · exact Or.inl ((mem_insertIf ..).mpr (.inl h))
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl ((mem_insertIf ..).mpr (.inr ⟨hn,rfl,rfl⟩))
        · exact .inr h
  exact aux _ _ (h.imp_right Array.mem_toList_iff.mpr)

theorem index_covers (needed : Prefix → Bool) (rows : Array Cube) {r w : Cube} (hr : r ∈ rows)
    (hw : w ∈ orbitImages r) (hn : needed (prefixOf w) = true) :
    w ∈ (indexPrefixes orbitImages needed rows).getD (prefixOf w) #[] := by
  let put (m : Index) (a : Cube) := (orbitImages a).foldl (insertIf needed) m
  have aux (xs : List Cube) (m : Index) (h : w ∈ m.getD (prefixOf w) #[] ∨ r ∈ xs) :
      w ∈ (xs.foldl put m).getD (prefixOf w) #[] := by
    induction xs generalizing m with
    | nil => simpa using h
    | cons a xs ih =>
      apply ih
      rcases h with h | h
      · exact Or.inl (orbit_add needed _ _ _ hn (.inl h))
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl (orbit_add needed _ _ _ hn (.inr hw))
        · exact .inr h
  simpa only [indexPrefixes, ← Array.foldl_toList, put] using
    aux rows.toList {} (.inr (Array.mem_toList_iff.mpr hr))

theorem prefix_of_band {C : SearchSpec.Points} {s t u w : Cube} {p : Port}
    (hs : TypeThree.RepresentsBand C 0 0 s) (ht : TypeThree.RepresentsBand C 0 1 t)
    (hu : cubeSet u = projectedLevel C 0 1)
    (hw : TypeThree.RepresentsBand C p.axis.succ p.start w) :
    prefixOf w = request s t u p := by
  have h0 := Contacts.crossing p.axis hs hw
  have h1 := Contacts.crossing p.axis ht hw
  have h2 := Contacts.middle_window hu p.axis p.start hw
  change Prefix.mk (TypeThree.fastCut w 0 0) (TypeThree.fastCut w 0 1) (Contacts.middle w) = _
  simp only [request, TypeThree.fastCut_eq] at h2 ⊢
  rw [h0, h1, h2]
  rfl

end SevenCycle.Adjacent.BandJoin

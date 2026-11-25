import SevenCycle.TypeThree.Index
import SevenCycleRuntime.Adaptive

/-! Soundness of grouping sources by their two selected query slots. -/

namespace SevenCycle.TypeThree

private theorem queryIndex_eq (rows : Array CutRow) (ij : SlotPair) :
    queryIndex rows (makeIndex CutRow.a0 CutRow.a3 rows) ij =
    makeIndex (slot · ij.1) (slot · ij.2) rows := by
  by_cases e : ij = (0,1)
  · subst ij
    rfl
  · simp [queryIndex, e]

theorem adaptiveSources_sound (choose : Index → Array CutRow → CutRow → SlotPair)
    (sources rows : Array CutRow) (h : adaptiveSources choose sources rows = true) :
    NoJoined sources rows := by
  intro s hs
  let d := makeIndex CutRow.a0 CutRow.a3 rows
  let pick := choose d rows
  let tagged := sources.map fun r => (pick r, r)
  let ij := pick s
  have hmem : s ∈ selected tagged ij :=
    Array.mem_filterMap.mpr ⟨(ij,s), Array.mem_map.mpr ⟨s, hs, rfl⟩, by simp⟩
  have ne := Array.isEmpty_eq_false_iff_exists_mem.mpr ⟨s, hmem⟩
  have hfirst := Array.all_eq_true'.mp h ij.1 (Array.mem_ofFn.mpr ⟨ij.1, rfl⟩)
  have hgroup := Array.all_eq_true'.mp hfirst ij.2 (Array.mem_ofFn.mpr ⟨ij.2, rfl⟩)
  change (if (selected tagged ij).isEmpty then true else
    (selected tagged ij).all (rejectsSource d (queryIndex rows d ij) ij.1 ij.2)) = true at hgroup
  simp only [ne, Bool.false_eq_true, if_false, d, queryIndex_eq] at hgroup
  exact checkSources_sound _ _ _ _ hgroup s hmem

theorem checkAdaptive_sound (sources rows : Array CutRow)
    (h : checkAdaptive sources rows = true) : NoJoined sources rows :=
  adaptiveSources_sound (fun d all => leastSlots (estimateSlots d all)) sources rows h

/-- The part assigned to a particular source, defined against the whole domain. -/
def sourcePart (rows : Array CutRow) (s : CutRow) : Fin 5 :=
  slotPart (leastSlots (estimateSlots (makeIndex CutRow.a0 CutRow.a3 rows) rows) s)

/-- A single successful part excludes any joint configuration whose source
has that part. `actual_joined` supplies such a configuration for an actual code. -/
theorem checkPart_sound (p : Fin 5) (sources rows : Array CutRow)
    (h : checkPart p sources rows = true) :
    NoJoined (sources.filter (fun s => sourcePart rows s == p)) rows := by
  intro s hm
  obtain ⟨hs, hp⟩ := Array.mem_filter.mp hm
  let d := makeIndex CutRow.a0 CutRow.a3 rows
  let cost := estimateSlots d rows
  let tagged := tagByCost cost sources
  let ij := leastSlots cost s
  have he : slotPart ij = p := beq_iff_eq.mp hp
  have hmem : s ∈ selected tagged ij :=
    Array.mem_filterMap.mpr ⟨(ij,s), Array.mem_map.mpr ⟨s, hs, rfl⟩, by simp⟩
  have ne := Array.isEmpty_eq_false_iff_exists_mem.mpr ⟨s, hmem⟩
  have hfirst := Array.all_eq_true'.mp h ij.1 (Array.mem_ofFn.mpr ⟨ij.1, rfl⟩)
  have hgroup := Array.all_eq_true'.mp hfirst ij.2 (Array.mem_ofFn.mpr ⟨ij.2, rfl⟩)
  change (!(slotPart ij == p) || (if (selected tagged ij).isEmpty then true else
    (selected tagged ij).all (rejectsSource d (queryIndex rows d ij) ij.1 ij.2))) = true at hgroup
  simp only [he, beq_self_eq_true, Bool.not_true, Bool.false_or, ne, Bool.false_eq_true,
    if_false, d, queryIndex_eq] at hgroup
  exact checkSources_sound _ _ _ _ hgroup s hmem

/-- Each source has a chosen pair, and its pair has a part. Consequently the
five successful results cover the same search as the single global call. -/
theorem checkAdaptive_of_parts (sources rows : Array CutRow)
    (h : ∀ p, checkPart p sources rows = true) : checkAdaptive sources rows = true := by
  apply Array.all_eq_true'.mpr
  intro i hi
  apply Array.all_eq_true'.mpr
  intro j hj
  have h1 := Array.all_eq_true'.mp (h (slotPart (i,j))) i hi
  have h2 := Array.all_eq_true'.mp h1 j hj
  simpa only [beq_self_eq_true, Bool.not_true, Bool.false_or] using h2

end SevenCycle.TypeThree

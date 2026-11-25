import SevenCycle.Adjacent.MiddleJoin
import SevenCycle.Adjacent.Sites

namespace SevenCycle.Adjacent.Middle

open Proof Blueprint Bitsets

private theorem window_iff (v : Site) (k : Fin 3) (j : Contacts.Height) :
    inWindow k j v = true ↔ v.word k = j ∨ v.word k = (j+1 : Contacts.Height) := by
  have eq : axisValue k v = v.word k := by fin_cases k <;> rfl
  have same : ∀ z j : Fin 7, (z == j || z == j+1) = true ↔
      (show ZMod 7 from z) = j ∨ (show ZMod 7 from z) = (j+1 : Fin 7) := by decide
  exact (eq ▸ same (axisValue k v) j)

private theorem id_project (v : Site) (a : Fin 3) :
    Bitsets.index (dropCoord a v.word) = projectedIndex a v := by fin_cases a <;> rfl

/-- Within an independent anchor each transverse two-level projection is
injective; an actual selected middle mask therefore selects exactly the
corresponding anchor sites inside the window. -/
private theorem picked (s u : Cube) (hs : packing cycleStep (cubeSet s)) (hu : cubeSet u ⊆ cubeSet s)
    (a : Fin 3) (j : Contacts.Height) (v : Site) (hv : v ∈ sites s) (hj : inWindow a j v = true) :
    (TypeThree.fastCut u a j).toNat.testBit (projectedIndex a v) = occupied u v := by
  apply Bool.eq_iff_iff.mpr
  rw [← id_project v a, TypeThree.fastCut_eq]
  change planeMem (cut u a j) (dropCoord a v.word) = true ↔ _
  rw [← mem_planeSet, planeSet_cut, occupied_iff]
  have hvs := (occupied_iff s v).mp ((mem_sites v s).mp hv)
  have win := (window_iff v a j).mp hj
  constructor
  · rintro h
    obtain ⟨x, hh, e⟩ := Finset.mem_image.mp h
    obtain ⟨hx, xwin⟩ := Finset.mem_filter.mp hh
    have eq : x = v.word := (Bands.band_projection hs a j).1
      (Finset.mem_filter.mpr ⟨hu hx, xwin⟩) (Finset.mem_filter.mpr ⟨hvs, win⟩) e
    exact eq ▸ hx
  · intro h
    exact Finset.mem_image.mpr ⟨v.word, Finset.mem_filter.mpr ⟨h,win⟩,rfl⟩

theorem choice_contains (atlas : Contacts.AtlasComplete)
    {C : SearchSpec.Points} (hC : packing cycleStep C) {s t u : Cube}
    (hs : TypeThree.RepresentsBand C 0 0 s) (ht : TypeThree.RepresentsBand C 0 1 t)
    (hu : cubeSet u = projectedLevel C 0 1) (sub : cubeSet u ⊆ cubeSet s)
    {a : Fin 3} {j : Contacts.Height} (full : j ∈ fullStarts C a.succ) :
    let options := choices (sites s) s t (Contacts.index orbitImages atlasPlanes) a j
    flags (sites s) (occupied u) &&& options.scope ∈ options.picks := by
  have packingS : packing cycleStep (cubeSet s) := hs ▸ (Bands.band_projection hC 0 0).2
  apply Array.mem_map.mpr
  refine ⟨TypeThree.fastCut u a j, Contacts.middle_entry atlas hC hs ht hu full, ?_⟩
  dsimp only [choices]
  rw [flags_and]
  apply flags_congr
  intro v hv
  cases hw : inWindow a j v
  · simp
  · simp [picked s u packingS sub a j v hv hw]

theorem subBoth {C : SearchSpec.Points} {s t u : Cube}
    (hs : TypeThree.RepresentsBand C 0 0 s) (ht : TypeThree.RepresentsBand C 0 1 t)
    (hu : cubeSet u = projectedLevel C 0 1) : cubeSet u ⊆ cubeSet s ∧ cubeSet u ⊆ cubeSet t := by
  rw [hs,ht,hu]
  constructor <;> apply Finset.image_mono <;> intro w hw
  · obtain ⟨h,e⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨h, Or.inr e⟩
  · obtain ⟨h,e⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨h, Or.inl e⟩

theorem count_eq (u : Cube) : count u = (cubeSet u).card := by
  rw [← cubeCard_eq]
  simp only [count, ← Adjacent.maskCard_eq, cubeCard]

/-- For an actual code the executable six-window join visits the physical
middle layer at the anchor's common height. Its continuation receives a cube
representing that layer in the original coordinates. -/
theorem checkMiddle_sound (atlas : Contacts.AtlasComplete)
    {C : SearchSpec.Points} (hC : packing cycleStep C) {s t u : Cube}
    (hs : TypeThree.RepresentsBand C 0 0 s) (ht : TypeThree.RepresentsBand C 0 1 t)
    (hu : cubeSet u = projectedLevel C 0 1) (hlo : 16 ≤ (cubeSet u).card) (hhi : (cubeSet u).card ≤ 19)
    (gaps cs : Vector Contacts.Height 3)
    (full : ∀ a : Fin 3, cs.get a ∈ fullStarts C a.succ ∧ cs.get a - gaps.get a ∈ fullStarts C a.succ)
    {next : Cube → Bool}
    (ok : checkMiddle s t (Contacts.index orbitImages atlasPlanes) gaps cs next = true) :
    ∃ r : Cube, cubeSet r = projectedLevel C 0 1 ∧ next r = true := by
  let xs := sites s
  let bits := flags xs (occupied u)
  let valid := flags xs (occupied t)
  obtain ⟨subS,subT⟩ := subBoth hs ht hu
  have sub : bits &&& valid = bits := by
    unfold bits valid
    rw [flags_and]
    apply flags_congr
    intro v _
    cases hv : occupied u v
    · rfl
    · simp [(occupied_iff t v).mpr (subT ((occupied_iff u v).mp hv))]
  have hsize := flags_bound xs (occupied u)
  let row := choices xs s t (Contacts.index orbitImages atlasPlanes)
  let wins := ((Array.finRange 3).flatMap fun a =>
    #[row a (cs.get a - gaps.get a), row a (cs.get a)])
  have hits : ∀ w ∈ wins, bits &&& w.scope ∈ w.picks := by
    intro w hw
    obtain ⟨a, _, hm⟩ := Array.mem_flatMap.mp hw
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact choice_contains atlas hC hs ht hu subS (full a).2
    · exact choice_contains atlas hC hs ht hu subS (full a).1
  let last := fun m =>
    let pop := count (materialize xs m)
    decide (pop < 16) || decide (19 < pop) || next (materialize xs m)
  have result := join_sound valid bits xs.size sub hsize last wins hits 0 (by simpa using ok)
  have decode := materialize_correct s u subS
  change cubeSet (materialize xs bits) = cubeSet u at decode
  refine ⟨_,decode.trans hu,?_⟩
  have pop : count (materialize xs bits) = (cubeSet u).card := (count_eq _).trans (congrArg Finset.card decode)
  simpa only [last, pop, decide_eq_false (Nat.not_lt.mpr hlo), decide_eq_false (Nat.not_lt.mpr hhi), Bool.false_or] using result

end SevenCycle.Adjacent.Middle

import SevenCycle.Blueprint.Definitions
import SevenCycle.TypeThree.Join

/-! # From projected bands to the exact join

The lemmas compare the packed masks with the same physical coordinates of C.
The order of the two retained coordinates is checked for each pair of axes. -/

namespace SevenCycle.TypeThree
open SevenCycle.Proof (Tuple)

abbrev RepresentsBand (C : Finset (Tuple 4)) (k : Fin 4) (s : ZMod 7)
    (r : Bitsets.Cube) := Bitsets.cubeSet r = Blueprint.projectedBand C k s

private theorem mem_projection {n : ℕ} {D : Finset (Tuple (n+1))}
    {k : Fin (n+1)} {t : ZMod 7} {z : Tuple n} :
    z ∈ Blueprint.projectedBand D k t ↔
      ∃ x ∈ D, (x k = t ∨ x k = t+1) ∧ Blueprint.dropCoord k x = z := by
  simp [Blueprint.projectedBand, Blueprint.band, and_assoc]

private theorem rearrange {C : Finset (Tuple 4)} {k l : Fin 4} {i j : Fin 3}
    (hs : k.succAbove i = l) (ht : l.succAbove j = k)
    (ho : ∀ a : Fin 2, k.succAbove (i.succAbove a) = l.succAbove (j.succAbove a))
    (s t : ZMod 7) :
    Blueprint.projectedBand (Blueprint.projectedBand C k s) i t ⊆
      Blueprint.projectedBand (Blueprint.projectedBand C l t) j s := by
  intro x hx
  obtain ⟨u, hu, hit, rfl⟩ := mem_projection.mp hx
  obtain ⟨v, hv, hks, rfl⟩ := mem_projection.mp hu
  refine mem_projection.mpr ⟨Blueprint.dropCoord l v, mem_projection.mpr ⟨v, hv, ?_, rfl⟩,
    ?_, ?_⟩
  · simpa only [Blueprint.dropCoord, hs] using hit
  · simpa only [Blueprint.dropCoord, ht] using hks
  · funext a
    exact congrArg v (ho a).symm

theorem equal_cuts {C : Finset (Tuple 4)} {k l : Fin 4} {i j : Fin 3}
    (hs : k.succAbove i = l) (ht : l.succAbove j = k)
    (ho : ∀ a : Fin 2, k.succAbove (i.succAbove a) = l.succAbove (j.succAbove a))
    {r w : Bitsets.Cube} {s t : ZMod 7} (hr : RepresentsBand C k s r)
    (hw : RepresentsBand C l t w) : Bitsets.cut r i t = Bitsets.cut w j s := by
  apply Bitsets.plane_eq_of_set_eq (Bitsets.canonical_cut _ _ _) (Bitsets.canonical_cut _ _ _)
  rw [Bitsets.planeSet_cut, Bitsets.planeSet_cut]
  change Blueprint.projectedBand (Bitsets.cubeSet r) i t =
    Blueprint.projectedBand (Bitsets.cubeSet w) j s
  rw [hr, hw]
  exact Finset.Subset.antisymm (rearrange hs ht ho s t)
    (rearrange ht hs (fun a => (ho a).symm) t s)

private theorem crossesAB {C : Finset (Tuple 4)} {r w : Bitsets.Cube} {s t : ZMod 7}
    (hr : RepresentsBand C 1 s r) (hw : RepresentsBand C 2 t w) :
    Bitsets.cut r 1 t = Bitsets.cut w 1 s :=
  equal_cuts (by decide) (by decide) (by decide) hr hw

private theorem crossesAC {C : Finset (Tuple 4)} {r w : Bitsets.Cube} {s t : ZMod 7}
    (hr : RepresentsBand C 1 s r) (hw : RepresentsBand C 3 t w) :
    Bitsets.cut r 2 t = Bitsets.cut w 1 s :=
  equal_cuts (by decide) (by decide) (by decide) hr hw

private theorem crossesBC {C : Finset (Tuple 4)} {r w : Bitsets.Cube} {s t : ZMod 7}
    (hr : RepresentsBand C 2 s r) (hw : RepresentsBand C 3 t w) :
    Bitsets.cut r 2 t = Bitsets.cut w 2 s :=
  equal_cuts (by decide) (by decide) (by decide) hr hw

theorem actual_crosses {C : Finset (Tuple 4)} {a a' b b' c c' : Bitsets.Cube}
    (ha : RepresentsBand C 1 0 a) (ha' : RepresentsBand C 1 3 a')
    (hb : RepresentsBand C 2 0 b) (hb' : RepresentsBand C 2 3 b')
    (hc : RepresentsBand C 3 0 c) (hc' : RepresentsBand C 3 3 c') :
    Crosses (cutsOf a) (cutsOf a') (cutsOf b) (cutsOf b') (cutsOf c) (cutsOf c') :=
  ⟨crossesAB ha hb, crossesAB ha' hb, crossesAB ha hb', crossesAB ha' hb',
   crossesAC ha hc, crossesAC ha' hc, crossesBC hb hc, crossesBC hb' hc,
   crossesAC ha hc', crossesAC ha' hc', crossesBC hb hc', crossesBC hb' hc'⟩

/-- All twenty-four equalities of a normalised type-three configuration. -/
theorem actual_joined {C : Finset (Tuple 4)} {s t a a' b b' c c' : Bitsets.Cube}
    (hs : RepresentsBand C 0 0 s) (ht : RepresentsBand C 0 3 t)
    (ha : RepresentsBand C 1 0 a) (ha' : RepresentsBand C 1 3 a')
    (hb : RepresentsBand C 2 0 b) (hb' : RepresentsBand C 2 3 b')
    (hc : RepresentsBand C 3 0 c) (hc' : RepresentsBand C 3 3 c') :
    Joined (cutsOf s) (cutsOf t) (cutsOf a) (cutsOf a') (cutsOf b) (cutsOf b')
      (cutsOf c) (cutsOf c') := by
  have eA {s t : ZMod 7} {u v : Bitsets.Cube}
      (hu : RepresentsBand C 1 s u) (hv : RepresentsBand C 0 t v) :
      Bitsets.cut u 0 t = Bitsets.cut v 0 s :=
    equal_cuts (by decide) (by decide) (by decide) hu hv
  have eB {s t : ZMod 7} {u v : Bitsets.Cube}
      (hu : RepresentsBand C 2 s u) (hv : RepresentsBand C 0 t v) :
      Bitsets.cut u 0 t = Bitsets.cut v 1 s :=
    equal_cuts (by decide) (by decide) (by decide) hu hv
  have eC {s t : ZMod 7} {u v : Bitsets.Cube}
      (hu : RepresentsBand C 3 s u) (hv : RepresentsBand C 0 t v) :
      Bitsets.cut u 0 t = Bitsets.cut v 2 s :=
    equal_cuts (by decide) (by decide) (by decide) hu hv
  exact ⟨⟨eA ha hs, eA ha ht⟩, ⟨eA ha' hs, eA ha' ht⟩,
    ⟨eB hb hs, eB hb ht⟩, ⟨eB hb' hs, eB hb' ht⟩,
    ⟨eC hc hs, eC hc ht⟩, ⟨eC hc' hs, eC hc' ht⟩,
    actual_crosses ha ha' hb hb' hc hc'⟩

end SevenCycle.TypeThree

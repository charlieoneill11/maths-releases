import SevenCycle.TypeTwo.Join
import SevenCycle.TypeThree.Coverage
import SevenCycle.Bitsets.Orbit
import Std.Data.HashMap.Lemmas

/-! ## Atlas domains for the planar and projection filters

Once the anchor is axis zero with full starts zero and two, its coordinate is
the first surviving coordinate in every transverse cube. The two cuts on that
coordinate index all candidates for one transverse band.
-/

namespace SevenCycle.TypeTwo

open Proof Blueprint Blueprint.SearchSpec Proof.FrameGeometry
open Bitsets (Cube Plane)

abbrev PairKey := Plane × Plane
abbrev DomainIndex := Std.HashMap PairKey (Array Cube)
abbrev CutFn := Cube → Fin 3 → Height → Plane

@[inline] def keyOf (cut : CutFn) (r : Cube) : PairKey := (cut r 0 0, cut r 0 2)

@[inline] def bucket (m : DomainIndex) (key : PairKey) : Array Cube := m.getD key #[]

private def add (cut : CutFn) (m : DomainIndex) (w : Cube) : DomainIndex :=
  m.alter (keyOf cut w) fun v => some ((v.getD #[]).push w)

private theorem mem_add (cut : CutFn) (m : DomainIndex) (w r : Cube) (a : PairKey) :
    r ∈ bucket (add cut m w) a ↔ r ∈ bucket m a ∨ keyOf cut w = a ∧ r = w := by
  by_cases hh : keyOf cut w = a
  · subst a
    simp [add, bucket, Std.HashMap.getD_eq_getD_getElem?]
  · simp only [add, bucket, Std.HashMap.getD_alter, beq_iff_eq, hh, if_false, false_and, or_false]

private def insertOrbit (cut : CutFn) (m : DomainIndex) (r : Cube) : DomainIndex :=
  (Bitsets.orbitImages r).foldl (add cut) m

/-- Build domains one input class at a time. Only the requested array of
representatives is traversed, allowing independent candidate-domain benchmarks. -/
def makeDomains (cut : CutFn) (rows : Array Cube) : DomainIndex :=
  rows.foldl (insertOrbit cut) {}

private theorem insertOrbit_contains (cut : CutFn) (m : DomainIndex) (r w : Cube) (key : PairKey)
    (h : w ∈ bucket m key ∨ w ∈ Bitsets.orbitImages r ∧ keyOf cut w = key) :
    w ∈ bucket (insertOrbit cut m r) key := by
  let ims := Bitsets.orbitImages r
  have all := Array.foldl_induction (as := ims) (f := add cut) (init := m)
    (motive := fun i tbl => w ∈ bucket m key ∨ (∃ j : Fin ims.size, j.val < i ∧ ims[j] = w) ∧
      keyOf cut w = key → w ∈ bucket tbl key)
    (by rintro (hm | ⟨⟨j,hj,_⟩,_⟩); exact hm; omega) (by
      intro i tbl ih h
      apply (mem_add ..).2
      rcases h with hm | ⟨⟨j,hj,hw⟩, hkey⟩
      · exact Or.inl (ih (Or.inl hm))
      · by_cases eq : i = j
        · subst j
          exact Or.inr ⟨hw ▸ hkey, hw.symm⟩
        · have : i.val ≠ j.val := fun e => eq (Fin.ext e)
          exact Or.inl (ih (Or.inr ⟨⟨j, by omega, hw⟩, hkey⟩)))
  apply all
  rcases h with hm | ⟨hw,hkey⟩
  · exact Or.inl hm
  · obtain ⟨j,hj,h⟩ := Array.mem_iff_getElem.mp hw
    exact Or.inr ⟨⟨⟨j,hj⟩,hj,h⟩,hkey⟩

theorem collect_covers {α β γ : Type*} (gen : α → Array β) (put : γ → α → γ)
    (has : γ → Prop) (w : β) (hput : ∀ m a, has m ∨ w ∈ gen a → has (put m a))
    (as : Array α) (init : γ) (a : α) (ha : a ∈ as) (hw : w ∈ gen a) :
    has (as.foldl put init) := by
  have all := Array.foldl_induction (as := as) (f := put) (init := init)
    (motive := fun i tbl => ∀ j : Fin as.size, j.val < i → w ∈ gen as[j.val] → has tbl)
    (by intro j h; exact False.elim (Nat.not_lt_zero _ h)) (by
      intro i tbl ih j hj hmem
      apply hput
      by_cases eq : i = j
      · subst j
        exact Or.inr hmem
      · have : i.val ≠ j.val := fun e => eq (Fin.ext e)
        exact Or.inl (ih j (by omega) hmem))
  obtain ⟨j,hj,rfl⟩ := Array.mem_iff_getElem.mp ha
  exact all ⟨j,hj⟩ hj hw

theorem makeDomains_covers (cut : CutFn) (rows : Array Cube) {r w : Cube}
    (hr : r ∈ rows) (hw : w ∈ Bitsets.orbitImages r) :
    w ∈ bucket (makeDomains cut rows) (keyOf cut w) := by
  apply collect_covers Bitsets.orbitImages (insertOrbit cut) (fun m => w ∈ bucket m (keyOf cut w))
    w _ rows {} r hr hw
  intro m a h
  exact insertOrbit_contains cut m a w _ (h.imp_right (fun h' => ⟨h',rfl⟩))

/-- One marked transverse band in the three surviving physical coordinates. -/
structure Contact where
  axis : Fin 3
  start : Height

def contactSlot (c : Contact) : Slot := ⟨c.axis.succ, c.start⟩

def anchorKey (cut : CutFn) (s t : Cube) (c : Contact) : PairKey :=
  (cut s c.axis c.start, cut t c.axis c.start)

def domainsFor (cut : CutFn) (m : DomainIndex) (s t : Cube) (cs : Vector Contact 6) : Domains :=
  cs.map fun c => bucket m (anchorKey cut s t c)

private theorem crossing_coords : ∀ (a : Fin 3) (i : Fin 2),
    (0 : Fin 4).succAbove (a.succAbove i) = a.succ.succAbove ((0 : Fin 3).succAbove i) :=
  by decide

theorem crosses_transverse {C : Points} (a : Fin 3) {s t : Height} {r w : Cube}
    (h : TypeThree.RepresentsBand C 0 s r) (hw : TypeThree.RepresentsBand C a.succ t w) :
    Bitsets.cut r a t = Bitsets.cut w 0 s := by
  apply TypeThree.equal_cuts (i := a) (j := 0) _ _ (crossing_coords a) h hw
  · simp
  · exact (by decide : ∀ i : Fin 3, i.succ.succAbove 0 = 0) a

theorem stores_of_rep {C : Points} {l : Axis} {a : Height} {w : Cube}
    (h : TypeThree.RepresentsBand C l a w) : Stores w l (stripe C l a) := by
  intro u hu
  rw [← Bitsets.mem_cubeSet, h]
  constructor
  · intro hp
    obtain ⟨x,hx,hxu⟩ := Finset.mem_image.mp hp
    obtain ⟨hC,hxk⟩ := Finset.mem_filter.mp hx
    refine mem_face.mpr ⟨x,hC,hxk,funext ((Fin.forall_iff_succAbove l).mpr ⟨?_,?_⟩)⟩
    · simpa [setHeight] using hu.symm
    · intro j
      simpa [setHeight] using congrFun hxu j
  · intro hp
    obtain ⟨x,hx,hk,rfl⟩ := mem_face.mp hp
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx,hk⟩, (drop_setHeight l x 0).symm⟩

private theorem domains_get (cut : CutFn) (idx : DomainIndex) (s t : Cube) (cs : Vector Contact 6)
    (j : Fin 6) : (domainsFor cut idx s t cs)[j] = bucket idx (anchorKey cut s t cs[j]) :=
  Vector.getElem_map (xs := cs) (i := j.val) ..

private theorem slot_get (cs : Vector Contact 6) (j : Fin 6) :
    (cs.map contactSlot)[j] = contactSlot cs[j] := Vector.getElem_map (xs := cs) (i := j.val) ..

/-- Projecting an actual full band, then applying atlas completeness and the
verified orbit enumerator, puts a matching cube into its two-key domain. -/
theorem domainsFor_cover
    (atlas : ∀ D : Finset (Tuple 3), packing cycleStep D → D.card = 33 →
      ∃ q : Fin atlasPlanes.size, ∃ g : Isometry 3, D = actOnCode g (atlasRepresentative q))
    {C : Points} (hC : packing cycleStep C) (cut : CutFn) (hc : ∀ r k a, cut r k a = Bitsets.cut r k a)
    {s t : Cube} (hs : TypeThree.RepresentsBand C 0 0 s) (ht : TypeThree.RepresentsBand C 0 2 t)
    (cs : Vector Contact 6) (hf : ∀ j : Fin 6, cs[j].start ∈ fullStarts C cs[j].axis.succ) :
    CoversJoin C 0 (cs.map contactSlot) (domainsFor cut (makeDomains cut atlasPlanes) s t cs) := by
  intro j
  let c := cs[j]
  have hand := Bands.band_projection hC c.axis.succ c.start
  have hn : (projectedBand C c.axis.succ c.start).card = 33 :=
    (Finset.card_image_of_injOn hand.1).trans (Finset.mem_filter.mp (hf j)).2
  obtain ⟨q,g,hg⟩ := atlas _ hand.2 hn
  obtain ⟨w,hw,hspec⟩ := Bitsets.orbitImages_complete g atlasPlanes[q]
  have hwrep : TypeThree.RepresentsBand C c.axis.succ c.start w := hspec.trans hg.symm
  have heq : keyOf cut w = anchorKey cut s t c := by
    simp only [keyOf, anchorKey, hc, crosses_transverse c.axis hs hwrep,
      crosses_transverse c.axis ht hwrep]
  have hget := makeDomains_covers cut atlasPlanes (Array.getElem_mem q.isLt) hw
  rw [heq] at hget
  rw [slot_get, domains_get]
  exact ⟨Fin.succ_ne_zero _, w, hget, stores_of_rep hwrep⟩

end SevenCycle.TypeTwo

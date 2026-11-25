import SevenCycle.Atlas.NextPlane
import SevenCycle.Atlas.Prefix
import SevenCycle.Atlas.Patterns

/-! # Soundness of normalized plane-chain traversal -/

namespace SevenCycle.Atlas.CubePlanes

open Proof Blueprint Bitsets

def initialPlanes (C : Finset (Tuple 3)) : Nat → Array Plane
  | 0 => #[]
  | j+1 => (initialPlanes C j).push (plane C (j : ZMod 7))

@[simp] theorem initialPlanes_size (C : Finset (Tuple 3)) (j : Nat) :
    (initialPlanes C j).size = j := by induction j <;> simp_all [initialPlanes]

theorem initialPlanes_get (C : Finset (Tuple 3)) (j i : Nat) (hi : i < (initialPlanes C j).size) :
    (initialPlanes C j)[i] = plane C (i : ZMod 7) := by
  induction j with
  | zero => simp at hi
  | succ j ih =>
    simp only [initialPlanes, Array.getElem_push]
    split
    · exact ih ‹_›
    · have : i = j := by simp only [initialPlanes_size] at *; omega
      rw [this]

private theorem prefix_subset (C : Finset (Tuple 3)) (j : Nat) : cubeSet (prefixCube (initialPlanes C j)) ⊆ C := by
  apply prefixCube_subset
  intro i hi
  rw [initialPlanes_get]
  have castId : ∀ j : Fin 7, ((j.val : Nat) : ZMod 7) = (show ZMod 7 from j) := by decide
  rw [castId]

theorem initialPlanes_complete (C : Finset (Tuple 3)) :
    cubeSet (prefixCube (initialPlanes C 7)) = C := by
  apply Finset.Subset.antisymm (prefix_subset ..)
  intro x hx
  apply (mem_cubeSet ..).mpr
  change planeMem ((prefixCube (initialPlanes C 7))[(x 0).val]'(x 0).isLt) (Fin.tail x)
  simp only [prefixCube, Vector.getElem_ofFn]
  have hi : (x 0).val < (initialPlanes C 7).size := by simpa using (x 0).val_lt
  rw [Array.getElem?_eq_getElem hi, Option.getD_some, initialPlanes_get]
  apply (mem_planeSet ..).mp
  simpa only [ZMod.natCast_zmod_val, mem_plane, Fin.cons_self_tail] using hx

def population (base : Nat) (d : ZMod 7 → Nat) (j : ZMod 7) :=
  base + d (j+1) + d (j+3) + d (j+5)

private def walk (prune : Nat → Array Plane → Bool) (base : Nat) (d : ZMod 7 → Nat) (finish : Cube → Bool)
    (first : Plane) (left j : Nat) (last : Plane) (stack : Array Plane) : Bool :=
  if !prune j stack then true
  else match left with
    | 0 => if compatible last first then finish (prefixCube stack) else true
    | n+1 =>
      visitNext last (population base d (j : ZMod 7)) (d ((j : ZMod 7)-1) == 0) fun q =>
        walk prune base d finish first n (j+1) q (stack.push q)

private theorem walk_sound (hplan : Planar.classificationCheck Planar.orbitIndices = true)
    {C : Finset (Tuple 3)} (hc : packing cycleStep C) (prune : Nat → Array Plane → Bool)
    (base : Nat) (d : ZMod 7 → Nat) (hprune : ∀ j, prune j (initialPlanes C j) = true) (hp : ∀ t, planeCard (plane C t) = population base d t)
    (hd : ∀ t, deficit C t = d t) (finish : Cube → Bool)
    (left j : Nat) (hl : left+j = 7)
    (h : walk prune base d finish (plane C 0) left j (plane C ((j : ZMod 7)-1)) (initialPlanes C j) = true) :
    finish (prefixCube (initialPlanes C 7)) = true := by
  induction left generalizing j with
  | zero =>
    have hj : j = 7 := by omega
    subst j
    have ok := hprune 7
    have hcomp : compatible (plane C (((7 : Nat) : ZMod 7)-1)) (plane C 0) := by
      convert adjacent_compatible hc (6 : ZMod 7) using 1
    simpa only [walk, ok, Bool.not_true, Bool.false_eq_true, if_false, hcomp, if_true] using h
  | succ n ih =>
    have ok := hprune j
    simp only [walk, ok, Bool.not_true, Bool.false_eq_true, if_false] at h
    have hj : (j : ZMod 7) - 1 + 1 = j := sub_add_cancel _ _
    have sz := hp (j : ZMod 7)
    rw [← hj] at sz
    have hfull (e : (d ((j : ZMod 7)-1) == 0) = true) : (band C 0 ((j : ZMod 7)-1)).card = 10 := by
      have e' := (hd ((j : ZMod 7)-1)).trans (beq_iff_eq.mp e)
      have hu := Bands.band_card_le card_le_ten C hc 0 ((j : ZMod 7)-1)
      change (band C 0 ((j : ZMod 7)-1)).card ≤ 10 at hu
      unfold deficit at e'
      omega
    have step := visitNext_sound hplan hc ((j : ZMod 7)-1) _
      (by simpa only [hj] using sz) _ hfull _ h
    apply ih (j+1) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, initialPlanes, hj] using step

/-- Exhaust the first split of the representative and all compatible subsequent levels. -/
def normalizedCheckUsing (prune : Nat → Array Plane → Bool) (r : Fin 3) (base : Nat) (d : ZMod 7 → Nat) (finish : Cube → Bool) : Bool :=
  let m := Planar.repMasks r
  (Completions.submasks m).all fun p =>
    if planeCard p = population base d 0 then
      let q := otherHalf m p
      walk prune base d finish p 5 2 q #[p,q]
    else true

theorem normalizedCheckUsing_sound (hplan : Planar.classificationCheck Planar.orbitIndices = true)
    {C : Finset (Tuple 3)} (hc : packing cycleStep C) (r : Fin 3)
    (norm : projectedBand C 0 0 = twoRepresentatives r) (prune : Nat → Array Plane → Bool)
    (base : Nat) (d : ZMod 7 → Nat) (hprune : ∀ j, prune j (initialPlanes C j) = true) (hp : ∀ t, planeCard (plane C t) = population base d t)
    (hd : ∀ t, deficit C t = d t) (finish : Cube → Bool)
    (ok : normalizedCheckUsing prune r base d finish = true) :
    finish (prefixCube (initialPlanes C 7)) = true := by
  have hm : planeSet (Planar.repMasks r) = planeSet (plane C 0) ∪ planeSet (plane C 1) := by
    rw [Planar.repMasks_correct, ← norm, plane_parts]
    simp
  have sub : planeSet (plane C 0) ⊆ planeSet (Planar.repMasks r) := by rw [hm]; exact Finset.subset_union_left
  have canon (t : ZMod 7) : Canonical (plane C t) := canonical_buildPlane _
  have he := Array.all_eq_true'.mp ok (plane C 0) (Completions.submasks_complete _ _ (canon _) sub)
  have hh : Disjoint (planeSet (plane C 0)) (planeSet (plane C 1)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (compatible_iff ..).mp (adjacent_compatible hc 0) x hx x (by simpa using hy) (fun _ => by simp [cycleStep])
  have heq := otherHalf_eq (Planar.repMasks_canonical r) (canon 1) hm hh
  simp only [hp, if_true, heq] at he
  exact walk_sound hplan hc prune base d hprune hp hd finish 5 2 (by decide) he

/-- The two-deficit search needs only the maximum-window prefix test. -/
def normalizedCheck (r : Fin 3) (base budget : Nat) (d : ZMod 7 → Nat) (finish : Cube → Bool) : Bool :=
  normalizedCheckUsing (fun _ a => prefixOK budget a) r base d finish

theorem normalizedCheck_sound (hplan : Planar.classificationCheck Planar.orbitIndices = true)
    {C : Finset (Tuple 3)} (hc : packing cycleStep C) (r : Fin 3)
    (norm : projectedBand C 0 0 = twoRepresentatives r) (base budget : Nat) (d : ZMod 7 → Nat)
    (hb : 70 ≤ 2*C.card + budget) (hp : ∀ t, planeCard (plane C t) = population base d t)
    (hd : ∀ t, deficit C t = d t) (finish : Cube → Bool)
    (ok : normalizedCheck r base budget d finish = true) : finish (prefixCube (initialPlanes C 7)) = true :=
  normalizedCheckUsing_sound hplan hc r norm (fun _ a => prefixOK budget a) base d
    (fun j => prefixOK_sound hplan hc (prefix_subset C j) hb) hp hd finish ok

/-- Test the 12 combinations of a first planar orbit and a cyclic deficit pattern. -/
def exclude34Check (jobs : Array (Fin 3 × Fin 4)) : Bool :=
  jobs.all fun (r, d) => normalizedCheck r 4 2 (pattern34 d) (fun _ => false)

theorem exclude34Check_sound (hplan : Planar.classificationCheck Planar.orbitIndices = true)
    (jobs : Array (Fin 3 × Fin 4)) (ok : exclude34Check jobs = true)
    (D : Finset (Tuple 3)) (hc : packing cycleStep D) (hs : D.card = 34)
    (r : Fin 3) (hn : projectedBand D 0 0 = twoRepresentatives r)
    (d : Fin 4) (hd : ∀ i, deficit D i = pattern34 d i) (job : (r,d) ∈ jobs) : False := by
  have check := Array.all_eq_true'.mp ok _ job
  have hp (t : ZMod 7) : planeCard (plane D t) = population 4 (pattern34 d) t := by
    have h := plane_population hc t
    simp only [hd, hs] at h
    unfold population
    omega
  have he := normalizedCheck_sound hplan hc r hn 4 2 (pattern34 d) (by omega) hp hd _ check
  exact Bool.noConfusion he

end SevenCycle.Atlas.CubePlanes

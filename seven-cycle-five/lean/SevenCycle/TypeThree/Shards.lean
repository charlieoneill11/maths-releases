import SevenCycle.TypeThree.CheckAdaptive

/-! # Coverage of the twenty type-three search shards

The index of an atlas representative modulo four chooses a source strip.
Within that strip the two least expensive query slots choose one of five
parts. Every shard searches the full orbit table for the opposite anchor and
all six transverse supports. -/

namespace SevenCycle.TypeThree
open Blueprint Proof

def stripReps (strip : Fin 4) (reps : Array Bitsets.Cube) : Array Bitsets.Cube :=
  (Array.finRange reps.size).filterMap fun i =>
    if i.val % 4 = strip.val then some reps[i] else none

private theorem strip_covers {reps : Array Bitsets.Cube} {r : Bitsets.Cube}
    (hr : r ∈ reps) : ∃ strip, r ∈ stripReps strip reps := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hr
  refine ⟨⟨i % 4, Nat.mod_lt _ (by decide)⟩, Array.mem_filterMap.mpr
    ⟨⟨i, hi⟩, Array.mem_ofFn.mpr ⟨⟨i, hi⟩, rfl⟩, ?_⟩⟩
  simp

def checkShard (part : Fin 5) (strip : Fin 4) (reps : Array Bitsets.Cube) : Bool :=
  checkPart part (packRows (stripReps strip reps) Bitsets.translationImages)
    (packRows reps Bitsets.orbitImages)

theorem checkShard_sound {p : Fin 5} {strip : Fin 4} {reps : Array Bitsets.Cube}
    (h : checkShard p strip reps = true) :
    let rows := packRows reps Bitsets.orbitImages
    let roots := packRows (stripReps strip reps) Bitsets.translationImages
    NoJoined (roots.filter (fun s => sourcePart rows s == p)) rows :=
  checkPart_sound p _ _ h

/-- Every translated source is checked in its strip and its assigned part. -/
theorem noJoined_of_shards {reps : Array Bitsets.Cube}
    (h : ∀ p strip, checkShard p strip reps = true) :
    NoJoined (packRows reps Bitsets.translationImages) (packRows reps Bitsets.orbitImages) := by
  intro s hs
  obtain ⟨r, hr, hs⟩ := Array.mem_flatMap.mp hs
  obtain ⟨strip, hstrip⟩ := strip_covers hr
  let rows := packRows reps Bitsets.orbitImages
  let p := sourcePart rows s
  have hmem : s ∈ packRows (stripReps strip reps) Bitsets.translationImages :=
    Array.mem_flatMap.mpr ⟨r, hstrip, hs⟩
  apply checkShard_sound (h p strip) s
  exact Array.mem_filter.mpr ⟨hmem, beq_self_eq_true _⟩

theorem exclude_of_shards (atlas : AtlasComplete) (h : ∀ p strip, checkShard p strip atlasPlanes = true)
    (C : Finset (Tuple 4)) (hc : packing cycleStep C) :
    ¬ ∀ k, ∃ i ∈ fullStarts C k, i+3 ∈ fullStarts C k :=
  exclude_of_noJoined atlas
    (covers_collectRows Bitsets.translationImages fastCutsOf fastCutsOf_eq)
    (covers_collectRows Bitsets.orbitImages fastCutsOf fastCutsOf_eq)
    (noJoined_of_shards h) C hc

end SevenCycle.TypeThree

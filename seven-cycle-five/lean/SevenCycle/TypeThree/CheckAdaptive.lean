import SevenCycle.TypeThree.Adaptive
import SevenCycle.TypeThree.Exclusion
import SevenCycle.TypeThree.FastCuts

/-! # The all-class adaptive checker for Proposition 17

The input is the array of representatives. The same array supplies the two
tables: translations for the root and all signed affine images for the other
seven bands. Only the search order is adaptive. -/

namespace SevenCycle.TypeThree
open Blueprint Proof

def checkAll (reps : Array Bitsets.Cube) : Bool :=
  let sources := packRows reps Bitsets.translationImages
  let rows := packRows reps Bitsets.orbitImages
  checkAdaptive sources rows

/-- One of five parts of the complete search, with
three of the fifteen increasing query pairs assigned to every part. -/
def checkDomainGroup (part : Fin 5) (reps : Array Bitsets.Cube) : Bool :=
  let sources := packRows reps Bitsets.translationImages
  let rows := packRows reps Bitsets.orbitImages
  checkPart part sources rows

theorem checkDomainGroup_sound (p : Fin 5) (reps : Array Bitsets.Cube)
    (h : checkDomainGroup p reps = true) :
    let rows := packRows reps Bitsets.orbitImages
    let roots := packRows reps Bitsets.translationImages
    NoJoined (roots.filter (fun s => sourcePart rows s == p)) rows :=
  checkPart_sound p (packRows reps Bitsets.translationImages) (packRows reps Bitsets.orbitImages) h

theorem checkAll_of_groups (reps : Array Bitsets.Cube)
    (h : ∀ p, checkDomainGroup p reps = true) : checkAll reps = true :=
  checkAdaptive_of_parts _ _ h

theorem checkAll_sound (h : checkAll atlasPlanes = true) (atlas : AtlasComplete)
    (C : Finset (Tuple 4)) (hc : packing cycleStep C) :
    ¬ ∀ k, ∃ i ∈ fullStarts C k, i+3 ∈ fullStarts C k :=
  exclude_of_noJoined atlas
    (covers_collectRows Bitsets.translationImages fastCutsOf fastCutsOf_eq)
    (covers_collectRows Bitsets.orbitImages fastCutsOf fastCutsOf_eq)
    (checkAdaptive_sound _ _ h) C hc

end SevenCycle.TypeThree

import SevenCycle.Blueprint

/-!
# Assembly of the public statements

The size-113 exclusion comes from the profile split. Band averaging lifts
any four-dimensional upper bound of 112 to a five-dimensional bound of 392.
-/

namespace SevenCycle.Proof

theorem bound_four (C : Finset (Tuple 4)) (hC : packing cycleStep C) : C.card ≤ 112 :=
  Blueprint.reduce_to_113 Blueprint.no_code_113 C hC

theorem five_of_four (h4 : ∀ C : Finset (Tuple 4), packing cycleStep C → C.card ≤ 112)
    (C : Finset (Tuple 5)) (hC : packing cycleStep C) : C.card ≤ 392 :=
  Blueprint.band_bound h4 C hC

end SevenCycle.Proof

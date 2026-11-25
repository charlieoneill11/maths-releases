import SevenCycle.Proof.Bands

/-! # The band upper bounds in the first two dimensions -/

namespace SevenCycle.Atlas

open Proof

/-- In zero dimensions there is just the empty word. -/
private theorem card_le_one (D : Finset (Tuple 0)) (_ : packing cycleStep D) : D.card ≤ 1 := by
  exact D.card_le_univ.trans_eq (by decide)

/-- Applying band averaging twice gives the upper bound in Lemma 6. -/
theorem card_le_ten (C : Finset (Tuple 2)) (hC : packing cycleStep C) : C.card ≤ 10 :=
  Bands.band_bound (Bands.band_bound card_le_one) C hC

end SevenCycle.Atlas

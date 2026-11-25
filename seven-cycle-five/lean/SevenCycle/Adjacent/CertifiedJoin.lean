import SevenCycle.Native.AdjacentSlabJoin
import SevenCycle.Adjacent.CertifiedExterior
import SevenCycle.Adjacent.Retention

namespace SevenCycle.Adjacent

open Blueprint Proof Blueprint.SearchSpec SlabJoin

/-- Stage 5 and the exterior bound for 1111, conditional on the output of the
six-band slab search in its normalized signed-permutation frame. -/
theorem framed1111_bound {C : Points} (hc : packing cycleStep C) (m : Frame)
    (hb : m.base = fun _ => 6) (hg : ∀ k, m.gap k = 1)
    (cover : ∀ k, ComesFrom SlabData.rows k (C.filter (inThree k))) : C.card ≤ 112 := by
  obtain ⟨bits, stored, known⟩ := checkFrames_sound hc SlabData.rows cover Native.adjacent1111_slab_join
  obtain ⟨row, hx, hrow⟩ := UnionMasks.knownUnionMasks_sound _ known
  have mid (k : Axis) : start m k true = 0 := by
    simp only [start, if_true, hb, hg, Nat.cast_one]
    decide
  have isin (k : Axis) (w : Tuple 4) : inSlab m k w ↔ inThree k w := by
    simp [inSlab, hb, mid, inThree]
  have within (w : Tuple 4) : inUnion m w ↔
      inThree 0 w ∨ inThree 1 w ∨ inThree 2 w ∨ inThree 3 w := by
    constructor
    · rintro ⟨k, _, h⟩
      have := (isin _ _).mp h
      fin_cases k <;> tauto
    · rintro (h|h|h|h)
      · exact ⟨0,hg 0,(isin 0 w).mpr h⟩
      · exact ⟨1,hg 1,(isin 1 w).mpr h⟩
      · exact ⟨2,hg 2,(isin 2 w).mpr h⟩
      · exact ⟨3,hg 3,(isin 3 w).mpr h⟩
  have decoded : C.filter (inUnion m) = rowSet (UnionTable.decode row).inside := by
    ext w
    obtain ⟨hj, hw⟩ := UnionMasks.components w
    have read : ∀ k, (bits k).testBit (address w) = true ↔ w ∈ C ∧ inThree k w := by
      intro k
      simpa only [hj, hw, true_and, Finset.mem_filter] using stored k (address w)
    have four := hrow (address w)
    simp only [Nat.testBit_or, Bool.or_eq_true_iff, read, hj, hw, true_and] at four
    rw [Finset.mem_filter, within, ← four]
    tauto
  let E := C \ C.filter (inUnion m)
  have he : SearchSpec.Exterior m (rowSet (UnionTable.decode row).inside) E :=
    decoded ▸ exterior hc m
  have h := UnionTable.table_bound row hx m hb hg E he
  rw [← decoded,Finset.union_sdiff_of_subset (Finset.filter_subset _ _)] at h
  exact h

end SevenCycle.Adjacent

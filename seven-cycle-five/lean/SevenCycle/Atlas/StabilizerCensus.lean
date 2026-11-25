import SevenCycle.Native.Stabilizers.Block0
import SevenCycle.Native.Stabilizers.Block1
import SevenCycle.Native.Stabilizers.Block2
import SevenCycle.Native.Stabilizers.Block3

namespace SevenCycle.Atlas.Stabilizers

open Blueprint

private theorem row_count : atlasPlanes.size = 1016 := by decide +kernel

theorem checkedOrder (i : Fin atlasPlanes.size) : stabilizerOrder i = orderHint i.val := by
  rw [← stabilizers_eq]
  have top : i.val < 1016 := lt_of_lt_of_le i.isLt row_count.le
  by_cases h0 : i.val < 254
  · exact blockCheck_sound _ Native.stabilizers_block0 i (by change 0 ≤ i.val; omega) (by change i.val < 0 + 254; omega)
  by_cases h1 : i.val < 508
  · exact blockCheck_sound _ Native.stabilizers_block1 i (by change 254 ≤ i.val; omega) (by change i.val < 254 + 254; omega)
  by_cases h2 : i.val < 762
  · exact blockCheck_sound _ Native.stabilizers_block2 i (by change 508 ≤ i.val; omega) (by change i.val < 508 + 254; omega)
  exact blockCheck_sound _ Native.stabilizers_block3 i (by change 762 ≤ i.val; omega) (by change i.val < 762 + 254; omega)

theorem census :
    let count := fun j : ℕ => (Finset.univ.filter fun r => stabilizerOrder r = j).card
    atlasPlanes.size = 1016 ∧ count 1 = 1011 ∧ count 2 = 1 ∧ count 3 = 3 ∧ count 6 = 1 := by
  refine ⟨row_count, ?_⟩
  simp only [checkedOrder]
  have count_eq (n : ℕ) (hn : n = 1016) :
      let count := fun j : ℕ => (Finset.univ.filter fun i : Fin n => orderHint i.val = j).card
      count 1 = 1011 ∧ count 2 = 1 ∧ count 3 = 3 ∧ count 6 = 1 := by
    subst n
    exact hint_histogram
  exact count_eq _ row_count

end SevenCycle.Atlas.Stabilizers

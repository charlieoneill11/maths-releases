import ZetaSixth.VolumeCoordinates
import Mathlib.Tactic.NormNum

namespace ZetaSixth

/-- The chamber in the original coordinates, with the largest coordinate innermost. -/
private def omegaCell : Cell :=
  ⟨0, 1, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0, 1⟩, ⟨1, 0, 0⟩⟩

private theorem omegaCell_set : omegaCell.set = Ω := by
  ext p
  simp only [omegaCell, Cell.set, Cell.kBand, Cell.xBand, Cell.zBand,
    Affine1.eval, Affine2.eval, Rat.cast_zero, Rat.cast_one, zero_add, one_mul,
    zero_mul, add_zero, Set.mem_setOf_eq, Set.mem_Ioo, Ω]
  constructor
  · rintro ⟨⟨hx, _⟩, ⟨hxy, _⟩, hyz, hz⟩
    exact ⟨hx, hxy, hyz, hz⟩
  · rintro ⟨hx, hxy, hyz, hz⟩
    exact ⟨⟨hx, hxy.trans (hyz.trans hz)⟩, ⟨hxy, hyz.trans hz⟩, hyz, hz⟩

private theorem omegaCell_ordered : omegaCell.Ordered := by
  apply omegaCell.ordered_of_corners <;> norm_num [omegaCell, Affine1.eval, Affine2.eval]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem omegaCell_integral : omegaCell.integrate densityPoly = 42 := by
  decide +kernel

/-- The ordered chamber has exact weighted mass 42, Lemma 4. -/
theorem mu_Omega : μ Ω = 42 := by
  rw [← omegaCell_set, mu_cell omegaCell omegaCell_ordered (by rw [omegaCell_set]),
    omegaCell_integral]
  norm_num

end ZetaSixth

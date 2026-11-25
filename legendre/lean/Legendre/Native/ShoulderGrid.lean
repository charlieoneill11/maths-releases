import Legendre.ShoulderGrid

namespace Legendre

theorem shoulderHead_check : checkShoulderHead shoulderHeightTable = true := by
  native_decide

/-- Lemma 20. The grid majorant is certified by the first-height Boolean test. -/
theorem shoulderHeight_steps : ShoulderSteps shoulderHeight :=
  shoulderHeight_steps_of_check shoulderHead_check

theorem twelve_mode_cell_bounds : ∃ e : ℕ → ℚ, ShoulderSteps e :=
  ⟨shoulderHeight, shoulderHeight_steps⟩

end Legendre

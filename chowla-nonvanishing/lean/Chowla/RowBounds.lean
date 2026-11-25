import Chowla.Stages

namespace Chowla

/-- Check the width restrictions using the rational input. The strict sum inequality
ensures a positive remaining radius for the Legendre profile. -/
def Rows.RowData.validWidths (r : Rows.RowData) : Bool :=
  r.widths.all (fun a => decide (0 < a ∧ a < 1)) && decide (r.widths.sum < 1)

theorem Rows.RowData.validWidths_sound (r : Rows.RowData) (h : r.validWidths = true) :
    (∀ a ∈ r.toRow.widths, a ∈ Set.Ioo (0 : ℝ) 1) ∧ r.toRow.widths.sum < 1 := by
  simp only [validWidths, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨ha, hs⟩ := h
  constructor
  · intro a hmem
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hmem
    specialize ha b hb
    exact ⟨by exact_mod_cast ha.1, by exact_mod_cast ha.2⟩
  · change (r.widths.map (fun q : ℚ => (q : ℝ))).sum < 1
    rw [← Rat.cast_list_sum]
    exact_mod_cast hs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem finalRows_widths_checked : finalRows.all Rows.RowData.validWidths = true := by
  decide +kernel

theorem finalRows_validWidths (r : Rows.RowData) (hr : r ∈ finalRows) :
    (∀ a ∈ r.toRow.widths, a ∈ Set.Ioo (0 : ℝ) 1) ∧ r.toRow.widths.sum < 1 :=
  r.validWidths_sound ((List.all_eq_true.mp finalRows_widths_checked) r hr)

end Chowla

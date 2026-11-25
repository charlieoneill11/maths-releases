import Chowla.CheckerRows
import Chowla.GridSound
import Chowla.Model.RowCumulant
import Chowla.StageSound

namespace Chowla.Checker

/-- The optimized central row bounds enclose the inner product defined by
the paper's model expectation. -/
theorem centralGrid_encloses_innerGRow (r : Rows.RowData) (hr : r.validWidths = true) :
    let b := centralGrid (GridSpline.pack hstarSpline) (prepareGrid r)
    (b.lower : ℝ) ≤ innerGRow r.toRow ∧ innerGRow r.toRow ≤ (b.upper : ℝ) := by
  obtain ⟨hwidths, hsum⟩ := r.validWidths_sound hr
  have hrow := r.toRow_admissible_of_widths hwidths hsum
  have hwidths' (a : ℚ) (ha : a ∈ r.widths) : (a : ℝ) ∈ Set.Ioo 0 1 :=
    hwidths (a : ℝ) (List.mem_map.mpr ⟨a, ha, rfl⟩)
  have hsum' : 0 < 1 - r.widths.sum := by
    simp only [Rows.RowData.validWidths, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact sub_pos.mpr hr.2
  rw [centralGrid_sound]
  by_cases hn : r.widths = []
  · have hnil := innerGRow_nil r.toRow hrow (by simp [Rows.RowData.toRow, hn])
    simp [central, centralFromSpline, prepare, hn, hnil]
  · have hne : r.toRow.widths ≠ [] := by
      cases hw : r.widths with
      | nil => exact (hn hw).elim
      | cons a A => simp [Rows.RowData.toRow, hw]
    rw [innerGRow_eq_cumulant r.toRow hrow hne]
    simpa only [Rows.RowData.toRow, List.map_map, Function.comp_def] using
      prepared_central_enclosure_sound r hsum' hn hwidths'

theorem centralRows_encloses_inner_G (rows : List Rows.RowData)
    (hvalid : rows.all Rows.RowData.validWidths = true) :
    let b := centralRows (rows.toArray.map prepareGrid)
    (b.lower : ℝ) ≤ inner_G (rows.map Rows.RowData.toRow) ∧
      inner_G (rows.map Rows.RowData.toRow) ≤ (b.upper : ℝ) :=
  centralRows_sound rows
    (fun r hr => (centralGrid_encloses_innerGRow r (List.all_eq_true.mp hvalid r hr)).1)
    (fun r hr => (centralGrid_encloses_innerGRow r (List.all_eq_true.mp hvalid r hr)).2)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem stageOneRows_validWidths :
    (stageOneLinear ++ stageOneQuadratic).all Rows.RowData.validWidths = true := by
  decide +kernel

private theorem stageOneCentral_eq_centralRows :
    stageOneCentral () =
      centralRows ((stageOneLinear ++ stageOneQuadratic).toArray.map prepareGrid) := by
  simp [stageOneCentral, centralRows, List.foldl_map, addCentralBounds]

theorem stageOneCentral_encloses :
    let F := (stageOneLinear ++ stageOneQuadratic).map Rows.RowData.toRow
    ((stageOneCentral ()).lower : ℝ) ≤ inner_G F ∧
      inner_G F ≤ ((stageOneCentral ()).upper : ℝ) := by
  rw [stageOneCentral_eq_centralRows]
  exact centralRows_encloses_inner_G _ stageOneRows_validWidths

end Chowla.Checker

import Chowla.CheckerStages
import Chowla.Model.Scaling
import Chowla.Amplitude

namespace Chowla.Checker

/-- Recover the rational input fields carried by a prepared row. -/
def GridRow.rowData (r : GridRow) : Rows.RowData :=
  ⟨r.row.widths, r.row.coefficients, r.row.weight⟩

/-- Interpret the rational inputs of a cached row in the real model. -/
noncomputable def GridRow.modelRow (r : GridRow) : Row := r.rowData.toRow

noncomputable def modelRows (rows : Array GridRow) : Amplitude :=
  rows.toList.map GridRow.modelRow

@[simp] theorem prepareGrid_rowData (r : Rows.RowData) : (prepareGrid r).rowData = r := by
  cases r
  rfl

@[simp] theorem prepareGrid_modelRow (r : Rows.RowData) : (prepareGrid r).modelRow = r.toRow := by
  simp [GridRow.modelRow]

@[simp] theorem prepareRows_toList (rows : List Rows.RowData) :
    (prepareRows rows).toList = rows.map prepareGrid := by
  simp [prepareRows]

@[simp] theorem prepareRows_modelRows (rows : List Rows.RowData) :
    modelRows (prepareRows rows) = rows.map Rows.RowData.toRow := by
  simp [modelRows, List.map_map, Function.comp_def]

@[simp] theorem modelRows_append (rows newRows : Array GridRow) :
    modelRows (rows ++ newRows) = modelRows rows ++ modelRows newRows := by
  simp [modelRows]

@[simp] theorem prepareRows_append (rows newRows : List Rows.RowData) :
    prepareRows (rows ++ newRows) = prepareRows rows ++ prepareRows newRows := by
  apply Array.ext'
  simp [prepareRows]

@[simp] theorem scaleGridRow_rowData (r : GridRow) (z : ℚ) :
    (scaleGridRow r z).rowData = { r.rowData with weight := z * r.rowData.weight } := rfl

@[simp] theorem scaleGridRow_prepareGrid (r : Rows.RowData) (z : ℚ) :
    scaleGridRow (prepareGrid r) z = prepareGrid { r with weight := z * r.weight } := rfl

@[simp] theorem scaleGridRow_modelRow (r : GridRow) (z : ℚ) :
    (scaleGridRow r z).modelRow = r.modelRow.scale (z : ℝ) := by
  simp only [GridRow.modelRow, scaleGridRow_rowData, Rows.RowData.toRow, Row.scale,
    Rat.cast_mul, mul_assoc]

@[simp] theorem modelRows_scale (rows : Array GridRow) (z : ℚ) :
    modelRows (rows.map (scaleGridRow · z)) = (modelRows rows).map (Row.scale (z : ℝ)) := by
  simp [modelRows, List.map_map, Function.comp_def]

/-- Weight changes leave the hypotheses for spline enclosures intact. -/
@[simp] theorem validWidths_setWeight (r : Rows.RowData) (w : ℚ) :
    ({ r with weight := w } : Rows.RowData).validWidths = r.validWidths := rfl

private theorem validWidths_map_weight (rows : List Rows.RowData) (z : ℚ) :
    (rows.map (fun r => { r with weight := z * r.weight })).all Rows.RowData.validWidths =
      rows.all Rows.RowData.validWidths := by
  simp [List.all_map, Function.comp_def]

private theorem published_validWidths :
    Rows.r0.all Rows.RowData.validWidths = true ∧
    Rows.r1Grid.all Rows.RowData.validWidths = true ∧
    Rows.r1Modes.all Rows.RowData.validWidths = true ∧
    Rows.r2.all Rows.RowData.validWidths = true ∧
    Rows.r3.all Rows.RowData.validWidths = true ∧
    Rows.r4.all Rows.RowData.validWidths = true ∧
    Rows.r5.all Rows.RowData.validWidths = true ∧
    Rows.r6.all Rows.RowData.validWidths = true ∧
    Rows.r7.all Rows.RowData.validWidths = true ∧
    Rows.r8.all Rows.RowData.validWidths = true ∧
    Rows.r9.all Rows.RowData.validWidths = true := by
  simpa only [finalRows, validWidths_map_weight, List.all_append, Bool.and_eq_true,
    and_assoc] using finalRows_widths_checked

theorem r0_validWidths : Rows.r0.all Rows.RowData.validWidths = true :=
  published_validWidths.1

theorem r1Grid_validWidths : Rows.r1Grid.all Rows.RowData.validWidths = true :=
  published_validWidths.2.1

theorem r1Modes_validWidths : Rows.r1Modes.all Rows.RowData.validWidths = true :=
  published_validWidths.2.2.1

theorem r2_validWidths : Rows.r2.all Rows.RowData.validWidths = true :=
  published_validWidths.2.2.2.1

theorem r3_validWidths : Rows.r3.all Rows.RowData.validWidths = true :=
  published_validWidths.2.2.2.2.1

theorem r4_validWidths : Rows.r4.all Rows.RowData.validWidths = true :=
  published_validWidths.2.2.2.2.2.1

theorem r5_validWidths : Rows.r5.all Rows.RowData.validWidths = true :=
  published_validWidths.2.2.2.2.2.2.1

theorem r6_validWidths : Rows.r6.all Rows.RowData.validWidths = true :=
  published_validWidths.2.2.2.2.2.2.2.1

theorem r7_validWidths : Rows.r7.all Rows.RowData.validWidths = true :=
  published_validWidths.2.2.2.2.2.2.2.2.1

theorem r8_validWidths : Rows.r8.all Rows.RowData.validWidths = true :=
  published_validWidths.2.2.2.2.2.2.2.2.2.1

theorem r9_validWidths : Rows.r9.all Rows.RowData.validWidths = true :=
  published_validWidths.2.2.2.2.2.2.2.2.2.2

theorem stageOneLinear_validWidths : stageOneLinear.all Rows.RowData.validWidths = true := by
  have hlow (r : Rows.RowData) : (splitStageOneRow r).1.validWidths = r.validWidths := rfl
  have hhigh (r : Rows.RowData) : (splitStageOneRow r).2.validWidths = r.validWidths := rfl
  simp [stageOneLinear, List.all_append, List.all_map, Function.comp_def,
    hlow, hhigh, r0_validWidths, r1Grid_validWidths, r1Modes_validWidths]

theorem stageOneQuadratic_validWidths : stageOneQuadratic.all Rows.RowData.validWidths = true :=
  r2_validWidths

private theorem validWidths_if (p : Prop) [Decidable p] {rows : List Rows.RowData}
    (h : rows.all Rows.RowData.validWidths = true) :
    (if p then rows else []).all Rows.RowData.validWidths = true := by
  split <;> simp_all

theorem initialStageRows_validWidths (stage : ℕ) :
    (initialStageRows stage).all Rows.RowData.validWidths = true := by
  simp [initialStageRows, List.all_append, r0_validWidths, r1Grid_validWidths, r1Modes_validWidths,
    r2_validWidths, validWidths_if _ r3_validWidths, validWidths_if _ r4_validWidths,
    validWidths_if _ r5_validWidths]

theorem firstFourRows_validWidths (stage : ℕ) :
    (firstFourRows stage).all Rows.RowData.validWidths = true := by
  simp [firstFourRows, List.all_append, stageOneLinear_validWidths, stageOneQuadratic_validWidths,
    validWidths_if _ r3_validWidths, validWidths_if _ r4_validWidths,
    validWidths_if _ r5_validWidths]

theorem stageRows_validWidths (i : Fin 8) :
    (stageRows i).all Rows.RowData.validWidths = true := by
  unfold stageRows
  split
  · exact initialStageRows_validWidths _
  · simp only [List.all_append, validWidths_map_weight, initialStageRows_validWidths,
      r6_validWidths, validWidths_if _ r7_validWidths, validWidths_if _ r8_validWidths,
      validWidths_if _ r9_validWidths, Bool.and_self]

/-- Any list of width-checked source rows defines an admissible amplitude. -/
theorem rows_isAmplitude {rows : List Rows.RowData}
    (h : rows.all Rows.RowData.validWidths = true) : IsAmplitude (rows.map Rows.RowData.toRow) := by
  intro r hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  obtain ⟨hwidths, hsum⟩ := q.validWidths_sound (List.all_eq_true.mp h q hq)
  exact q.toRow_admissible_of_widths hwidths hsum

theorem stageAmplitude_isAmplitude (i : Fin 8) : IsAmplitude (stageAmplitude i) :=
  rows_isAmplitude (stageRows_validWidths i)

/-- A valid grid row is the output of preparation on a width-checked input. -/
def GridRow.Valid (r : GridRow) : Prop :=
  prepareGrid r.rowData = r ∧ r.rowData.validWidths = true

@[simp] theorem prepareGrid_valid (r : Rows.RowData) :
    (prepareGrid r).Valid ↔ r.validWidths = true := by
  simp [GridRow.Valid]

theorem GridRow.Valid.scale {r : GridRow} (h : r.Valid) (z : ℚ) :
    (scaleGridRow r z).Valid := by
  refine ⟨?_, by simpa using h.2⟩
  rw [scaleGridRow_rowData, ← scaleGridRow_prepareGrid, h.1]

theorem GridRow.Valid.admissible {r : GridRow} (h : r.Valid) : r.modelRow.Admissible := by
  obtain ⟨hwidths, hsum⟩ := r.rowData.validWidths_sound h.2
  exact r.rowData.toRow_admissible_of_widths hwidths hsum

theorem modelRows_isAmplitude {rows : Array GridRow}
    (h : ∀ r ∈ rows.toList, GridRow.Valid r) : IsAmplitude (modelRows rows) := by
  intro k hk
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hk
  exact (h r hr).admissible

theorem prepareRows_valid {rows : List Rows.RowData} (h : rows.all Rows.RowData.validWidths = true)
    {r : GridRow} (hr : r ∈ (prepareRows rows).toList) : r.Valid := by
  rw [prepareRows_toList] at hr
  rw [List.mem_map] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  exact (prepareGrid_valid q).mpr (List.all_eq_true.mp h q hq)

theorem lateInherited_valid (stage : ℕ) {r : GridRow} (hr : r ∈ (lateInherited stage).toList) :
    r.Valid := by
  simp only [lateInherited, Array.toList_append, Array.toList_map, List.mem_append,
    List.mem_map] at hr
  rcases hr with ⟨q, hq, rfl⟩ | hr
  · exact (prepareRows_valid (firstFourRows_validWidths 4) hq).scale Rows.inheritedWeight
  · apply prepareRows_valid _ hr
    simp [List.all_append, r6_validWidths, validWidths_if _ r7_validWidths,
      validWidths_if _ r8_validWidths]

theorem modelRows_lateInherited (stage : ℕ) :
    modelRows (lateInherited stage) =
      ((firstFourRows 4).map Rows.RowData.toRow).map (Row.scale (Rows.inheritedWeight : ℝ)) ++
        (Rows.r6 ++ (if 7 ≤ stage then Rows.r7 else []) ++
          (if 8 ≤ stage then Rows.r8 else [])).map Rows.RowData.toRow := by
  simp only [lateInherited, modelRows_append, modelRows_scale, prepareRows_modelRows]

end Chowla.Checker

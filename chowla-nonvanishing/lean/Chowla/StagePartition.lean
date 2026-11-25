import Chowla.StageBlocks
import Chowla.StageCheck

namespace Chowla.Checker

/-- Sum a consecutive portion of a Gram increment while retaining the original
order and full earlier-row context. -/
def gramIncreaseBlock (old new : Array GridRow) (range : ℕ × ℕ) : ℚ := Id.run do
  let mut total := 0
  for i in [range.1 : min range.2 new.size] do
    total := total + gramContribution old new i
  return total

theorem gramIncreaseBlock_eq_sum (old new : Array GridRow) (range : ℕ × ℕ) :
    gramIncreaseBlock old new range =
      ((List.range' range.1 (min range.2 new.size - range.1)).map
        (gramContribution old new)).sum := by
  unfold gramIncreaseBlock
  rw [loop_sum]

theorem gramIncrease_eq_block (old new : Array GridRow) :
    gramIncrease old new = gramIncreaseBlock old new (0, new.size) := by
  unfold gramIncrease gramIncreaseBlock
  simp only [min_self]
  congr 1
  apply congrArg Id.run
  congr 2
  funext i acc
  cases h : new[i]? <;> simp [gramContribution, h, add_assoc]

/-- Adjacent blocks with bounded endpoints partition the full Gram increment. -/
theorem gramIncrease_eq_blocks (old new : Array GridRow) (cuts : List ℕ)
    (horder : (0 :: cuts).Pairwise (· ≤ ·)) (hend : cuts.getLastD 0 = new.size)
    (hstop : ∀ range ∈ (0 :: cuts).zip cuts, range.2 ≤ new.size) :
    gramIncrease old new =
      (((0 :: cuts).zip cuts).map (gramIncreaseBlock old new)).sum := by
  rw [gramIncrease_eq_block, gramIncreaseBlock_eq_sum]
  simp only [min_self]
  rw [← hend, sum_rangeByCuts (gramContribution old new) 0 cuts horder]
  congr 1
  apply List.map_congr_left
  intro range hr
  rw [gramIncreaseBlock_eq_sum, min_eq_left (hstop range hr)]

/-- Stages 6–8 use different new rows, and their cuts follow those rows' sizes. -/
def lateBlockRows (i : Fin 8) : List Rows.RowData :=
  match i.val with
  | 5 => Rows.r7
  | 6 => Rows.r8
  | 7 => Rows.r9
  | _ => []

def lateBlockCuts (i : Fin 8) : List ℕ :=
  match i.val with
  | 5 => [5, 8, 10, 13]
  | 6 => [10, 20, 35, 50, 65, 80, 95, 103]
  | 7 => [6, 12, 18, 26]
  | _ => []

def lateBlockRanges (i : Fin 8) : List (ℕ × ℕ) :=
  (0 :: lateBlockCuts i).zip (lateBlockCuts i)

def lateStageGramBlock (i : Fin 8) (range : ℕ × ℕ) : ℚ :=
  gramIncreaseBlock (lateInherited (i.val + 1)) (prepareRows (lateBlockRows i)) range

def lateStageGramBlockCheck (i : Fin 8) (range : ℕ × ℕ) (value : ℚ) : Bool :=
  decide (lateStageGramBlock i range = value)

def lateStageCentralCheck (i : Fin 8) (value : ℚ) : Bool :=
  decide ((centralRows (prepareRows (lateBlockRows i))).lower = value)

def lateStageBoundsFromBlocks (i : Fin 8) (previous : StageBounds) (center : ℚ)
    (grams : List ℚ) : StageBounds :=
  let base := if i.val = 5 then stageProportion 4 else previous.lowerProportion
  ⟨0, 0, 0, base + center - grams.sum / 2⟩

private theorem lateBlockCuts_order (i : Fin 8) :
    (0 :: lateBlockCuts i).Pairwise (· ≤ ·) := by
  fin_cases i <;> decide +kernel

private theorem lateBlockCuts_end (i : Fin 8) :
    (lateBlockCuts i).getLastD 0 = (prepareRows (lateBlockRows i)).size := by
  simp only [prepareRows, Array.size_map, List.size_toArray]
  fin_cases i <;> decide +kernel

private theorem lateBlockRanges_stop (i : Fin 8) (range : ℕ × ℕ)
    (h : range ∈ lateBlockRanges i) :
    range.2 ≤ (prepareRows (lateBlockRows i)).size := by
  have hb : (lateBlockRanges i).all
      (fun r => decide (r.2 ≤ (prepareRows (lateBlockRows i)).size)) = true := by
    simp only [prepareRows, Array.size_map, List.size_toArray]
    fin_cases i <;> decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hb range h)

theorem lateGram_eq_blocks (i : Fin 8) :
    gramIncrease (lateInherited (i.val + 1)) (prepareRows (lateBlockRows i)) =
      ((lateBlockRanges i).map (lateStageGramBlock i)).sum :=
  gramIncrease_eq_blocks _ _ _ (lateBlockCuts_order i) (lateBlockCuts_end i)
    (lateBlockRanges_stop i)

private theorem lateBlocks_eq_report (i : Fin 8) (ranges : List (ℕ × ℕ)) (values : List ℚ)
    (h : List.Forall₂ (fun range value => lateStageGramBlockCheck i range value = true)
      ranges values) :
    ranges.map (lateStageGramBlock i) = values := by
  induction h with
  | nil => rfl
  | cons h _ ih =>
    simp only [lateStageGramBlockCheck, decide_eq_true_eq] at h
    simp [h, ih]

private theorem lateStageBounds_eq_unpartitioned (i : Fin 8) (previous : StageBounds)
    (hi : 5 ≤ i.val) :
    evaluateStage i previous =
      let base := if i.val = 5 then stageProportion 4 else previous.lowerProportion
      let old := lateInherited (i.val + 1)
      let new := prepareRows (lateBlockRows i)
      ⟨0, 0, 0, base + (centralRows new).lower - gramIncrease old new / 2⟩ := by
  fin_cases i <;> norm_num at hi
  all_goals rfl

/-- All exact accepted blocks reproduce the corresponding original stage output. -/
theorem lateStageBounds_eq_report (i : Fin 8) (previous : StageBounds) (center : ℚ)
    (grams : List ℚ) (hi : 5 ≤ i.val)
    (hc : lateStageCentralCheck i center = true)
    (hg : List.Forall₂ (fun range value => lateStageGramBlockCheck i range value = true)
      (lateBlockRanges i) grams) :
    evaluateStage i previous = lateStageBoundsFromBlocks i previous center grams := by
  simp only [lateStageCentralCheck, decide_eq_true_eq] at hc
  rw [lateStageBounds_eq_unpartitioned i previous hi]
  dsimp only
  rw [hc, lateGram_eq_blocks i, lateBlocks_eq_report i _ _ hg]
  rfl

private theorem lateBlockRows_validWidths (i : Fin 8) :
    (lateBlockRows i).all Rows.RowData.validWidths = true := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact r7_validWidths
  · exact r8_validWidths
  · exact r9_validWidths

/-- The central block checker gives a lower bound on the added rows' contribution. -/
theorem lateStageCentralCheck_sound (i : Fin 8) (value : ℚ)
    (h : lateStageCentralCheck i value = true) :
    (value : ℝ) ≤ inner_G ((lateBlockRows i).map Rows.RowData.toRow) := by
  simp only [lateStageCentralCheck, decide_eq_true_eq] at h
  rw [← h]
  exact (centralRows_encloses_inner_G _ (lateBlockRows_validWidths i)).1

/-- An accepted rational Gram block equals its exact real Gram contribution. -/
theorem lateStageGramBlockCheck_sound (i : Fin 8) (range : ℕ × ℕ) (value : ℚ)
    (h : lateStageGramBlockCheck i range value = true) :
    let old := lateInherited (i.val + 1)
    let new := prepareRows (lateBlockRows i)
    (value : ℝ) =
      ((List.range' range.1 (min range.2 new.size - range.1)).map
        (modelGramContribution old new)).sum := by
  simp only [lateStageGramBlockCheck, decide_eq_true_eq] at h
  rw [← h, lateStageGramBlock, gramIncreaseBlock_eq_sum]
  dsimp only
  rw [Rat.cast_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  exact gramContribution_cast _ _ (fun _ hr => lateInherited_valid _ hr)
    (fun _ hr => prepareRows_valid (lateBlockRows_validWidths i) hr) j


/-- The exact block reports and the final rational comparison imply the
real enclosure for the stage. -/
theorem lateStageBlocks_sound (i : Fin 8) (previous : StageBounds) (center : ℚ) (grams : List ℚ)
    (hi : 5 ≤ i.val)
    (hc : lateStageCentralCheck i center = true)
    (hg : List.Forall₂ (fun range value => lateStageGramBlockCheck i range value = true)
      (lateBlockRanges i) grams)
    (hcheck : (lateStageBoundsFromBlocks i previous center grams).check i = true)
    (hprev : i.val ≠ 0 → previous.Sound (i - 1) ∧ previous.check (i - 1) = true) :
    (lateStageBoundsFromBlocks i previous center grams).Sound i ∧
      (lateStageBoundsFromBlocks i previous center grams).check i = true := by
  apply stageCheck_sound i previous _ _ hprev
  simp only [stageCheck, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨lateStageBounds_eq_report i previous center grams hi hc hg, hcheck⟩

end Chowla.Checker

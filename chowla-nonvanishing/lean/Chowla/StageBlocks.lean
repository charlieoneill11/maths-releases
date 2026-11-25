import Chowla.StageGram
import Chowla.StageCentral
import Chowla.StageRows
import Chowla.CheckerGram

namespace Chowla.Checker

open scoped BigOperators

/-- Consecutive endpoints for the independent checks of the linear row groups. -/
def stageOneLinearCuts : List ℕ :=
  [0, 80, 120, 160, 200, 240, 280, 320, 360, 400, 440, 480, 520, 560, 600, 640, 650]

def stageOneLinearRanges : List (ℕ × ℕ) := stageOneLinearCuts.zip stageOneLinearCuts.tail

def stageOneLinearGrid : Array GridRow := prepareRows stageOneLinear

def stageOneQuadraticGrid : Array GridRow := prepareRows stageOneQuadratic

def stageOneLinearBlock (range : ℕ × ℕ) : ℤ :=
  roundedLinearBlock stageOneLinearGrid stageOneQuadraticGrid range.1 range.2

def stageOneQuadraticBlock (_ : Unit) : ℤ :=
  roundedQuadraticBlock stageOneQuadraticGrid 0 stageOneQuadraticGrid.size

def stageOneLinearBlockCheck (range : ℕ × ℕ) (value : ℤ) : Bool :=
  decide (stageOneLinearBlock range = value)

def stageOneQuadraticBlockCheck (value : ℤ) : Bool :=
  decide (stageOneQuadraticBlock () = value)

def stageOneCentralCheck (lower upper : ℚ) : Bool :=
  let c := stageOneCentral ()
  decide (c.lower = lower ∧ c.upper = upper)

def stageOneBoundsFromBlocks (lower upper : ℚ) (linear : List ℤ) (quadratic : ℤ) : StageBounds :=
  ⟨lower, upper, ((linear.sum + quadratic : ℤ) : ℚ) / 100000000, 0⟩

private theorem linearBlock_eq_rangeSum (linear quadratic : Array GridRow) (a b : ℕ) :
    roundedLinearBlock linear quadratic a b =
      ((List.range' a (min b linear.size - a)).map fun i =>
        roundUpStageOne (gramContribution quadratic linear i)).sum := by
  rw [← loop_sum]
  unfold roundedLinearBlock
  congr 1
  apply congrArg Id.run
  congr 2
  funext i acc
  cases h : linear[i]? <;> simp [gramContribution, h, add_comm, roundUpStageOne_zero]

private theorem quadraticBlock_eq_rangeSum (rows : Array GridRow) (a b : ℕ) :
    roundedQuadraticBlock rows a b =
      ((List.range' a (min b rows.size - a)).map fun i =>
        roundUpStageOne (gramContribution #[] rows i)).sum := by
  rw [← loop_sum]
  unfold roundedQuadraticBlock
  congr 1
  apply congrArg Id.run
  congr 2
  funext i acc
  cases h : rows[i]? <;> simp [gramContribution, h, crossRow, roundUpStageOne_zero]

private theorem sum_rangeSplit {R : Type} [AddCommMonoid R] (f : ℕ → R) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    ((List.range' a (c - a)).map f).sum =
      ((List.range' a (b - a)).map f).sum + ((List.range' b (c - b)).map f).sum := by
  have hab' : a + (b - a) = b := by omega
  have hc : (b - a) + (c - b) = c - a := by omega
  have he := List.range'_append_1 (s := a) (m := b - a) (n := c - b)
  rw [hab', hc] at he
  rw [← he, List.map_append, List.sum_append]

theorem sum_rangeByCuts {R : Type} [AddCommMonoid R] (f : ℕ → R) (a : ℕ) (cuts : List ℕ)
    (h : (a :: cuts).Pairwise (· ≤ ·)) :
    ((List.range' a (cuts.getLastD a - a)).map f).sum =
      (((a :: cuts).zip cuts).map fun (b, c) => ((List.range' b (c - b)).map f).sum).sum := by
  induction cuts generalizing a with
  | nil => simp
  | cons b rest ih =>
    simp only [List.getLastD_cons, List.zip_cons_cons, List.map_cons, List.sum_cons]
    have hab : a ≤ b := (List.pairwise_cons.mp h).1 b (by simp)
    have htail := (List.pairwise_cons.mp h).2
    have hbc : b ≤ rest.getLastD b := by
      rcases List.mem_cons.mp (List.getLastD_mem_cons (l := rest) (a := b)) with he | he
      · exact he.symm.le
      · exact (List.pairwise_cons.mp htail).1 _ he
    rw [sum_rangeSplit f hab hbc, ih b htail]

set_option maxRecDepth 32768 in
private theorem stageOneLinearGrid_size : stageOneLinearGrid.size = 650 := by
  simp only [stageOneLinearGrid, prepareRows, Array.size_map, List.size_toArray]
  decide +kernel

private theorem stageOneLinearRanges_stop (range : ℕ × ℕ) (h : range ∈ stageOneLinearRanges) :
    range.2 ≤ 650 := by
  have hb : stageOneLinearRanges.all (fun r => decide (r.2 ≤ 650)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp hb range h)

/-- Adding the rounded groups over the cut ranges recovers the full linear sum. -/
theorem stageOneLinearBlocks_sum :
    (stageOneLinearRanges.map stageOneLinearBlock).sum =
      roundedLinearBlock stageOneLinearGrid stageOneQuadraticGrid 0 stageOneLinearGrid.size := by
  let f := fun i => roundUpStageOne (gramContribution stageOneQuadraticGrid stageOneLinearGrid i)
  rw [linearBlock_eq_rangeSum, min_self, stageOneLinearGrid_size]
  have hcut : stageOneLinearCuts.Pairwise (· ≤ ·) := by decide +kernel
  have h := sum_rangeByCuts f 0 stageOneLinearCuts.tail hcut
  rw [show stageOneLinearCuts.tail.getLastD 0 = 650 from rfl] at h
  rw [h]
  change (stageOneLinearRanges.map stageOneLinearBlock).sum = _
  congr 1
  apply List.map_congr_left
  intro range hr
  rw [stageOneLinearBlock, linearBlock_eq_rangeSum, stageOneLinearGrid_size,
    min_eq_left (stageOneLinearRanges_stop _ hr)]

private theorem linearBlocks_eq_report (ranges : List (ℕ × ℕ)) (values : List ℤ)
    (h : List.Forall₂ (fun range value => stageOneLinearBlockCheck range value = true)
      ranges values) : ranges.map stageOneLinearBlock = values := by
  induction h with
  | nil => rfl
  | cons h _ ih =>
    simp only [stageOneLinearBlockCheck, decide_eq_true_eq] at h
    simp [h, ih]

/-- The center proved in the independent check gives the real stage-one interval. -/
theorem stageOneCentralCheck_sound (lower upper : ℚ)
    (h : stageOneCentralCheck lower upper = true) :
    let F := (stageOneLinear ++ stageOneQuadratic).map Rows.RowData.toRow
    (lower : ℝ) ≤ inner_G F ∧ inner_G F ≤ (upper : ℝ) := by
  simp only [stageOneCentralCheck, decide_eq_true_eq] at h
  rw [← h.1, ← h.2]
  exact stageOneCentral_encloses

/-- Independently checked blocks assemble into the exact stage output. -/
theorem stageOneBounds_eq_report (lower upper : ℚ) (linear : List ℤ) (quadratic : ℤ)
    (hC : stageOneCentralCheck lower upper = true)
    (hL : List.Forall₂ (fun range value => stageOneLinearBlockCheck range value = true)
      stageOneLinearRanges linear)
    (hQ : stageOneQuadraticBlockCheck quadratic = true) :
    stageOneBounds () = stageOneBoundsFromBlocks lower upper linear quadratic := by
  simp only [stageOneCentralCheck, decide_eq_true_eq] at hC
  simp only [stageOneQuadraticBlockCheck, decide_eq_true_eq] at hQ
  change StageBounds.mk (stageOneCentral ()).lower (stageOneCentral ()).upper
    (((roundedLinearBlock stageOneLinearGrid stageOneQuadraticGrid 0 stageOneLinearGrid.size +
      stageOneQuadraticBlock () : ℤ) : ℚ) / 100000000) 0 = _
  rw [hC.1, hC.2, ← stageOneLinearBlocks_sum, linearBlocks_eq_report _ _ hL, hQ]
  rfl


private theorem gram_of_valid {r s : GridRow} (hr : r.Valid) (hs : s.Valid) :
    (gramGrid r s : ℝ) = innerRow r.modelRow s.modelRow := by
  unfold GridRow.modelRow
  rw [← hr.1, ← hs.1]
  exact gramGrid_eq_innerRow _ _ hr.2 hs.2

/-- The contribution of a row in a lower-triangular Gram sum, including its
interactions with the older amplitude. -/
noncomputable def modelGramContribution (old new : Array GridRow) (i : ℕ) : ℝ :=
  match new[i]? with
  | none => 0
  | some r =>
      let entry := fun q : Option GridRow => (q.map (fun s => innerRow r.modelRow s.modelRow)).getD 0
      2 * (∑ j ∈ Finset.range old.size, entry old[j]?) +
        (entry new[i]? + 2 * ∑ j ∈ Finset.range i, entry new[j]?)

theorem gramContribution_cast (old new : Array GridRow)
    (hold : ∀ r ∈ old.toList, GridRow.Valid r)
    (hnew : ∀ r ∈ new.toList, GridRow.Valid r) (i : ℕ) :
    (gramContribution old new i : ℝ) = modelGramContribution old new i := by
  unfold gramContribution modelGramContribution
  cases hi : new[i]? with
  | none => simp
  | some r =>
    have hr := hnew r (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hi))
    obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hi
    have castEntry (rows : Array GridRow) (hv : ∀ s ∈ rows.toList, GridRow.Valid s) (j : ℕ) :
        ((rows[j]?.map (gramGrid new[i])).getD 0 : ℝ) =
          (rows[j]?.map (fun s => innerRow new[i].modelRow s.modelRow)).getD 0 := by
      cases hj : rows[j]? with
      | none => simp
      | some s =>
        exact gram_of_valid hr (hv s (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hj)))
    rw [Rat.cast_add, crossRow_eq_sum]
    push_cast
    let ii : Fin new.size := ⟨i, hlt⟩
    rw [normRow_cast new ii new[i]]
    have hdiag : (gramGrid new[i] new[ii] : ℝ) =
        innerRow new[i].modelRow new[i].modelRow := gram_of_valid hr hr
    simp only [hdiag, ii, Option.map_some, Option.getD_some, castEntry old hold, castEntry new hnew]

private theorem modelGramBlock_upper (old new : Array GridRow) (indices : List ℕ)
    (hold : ∀ r ∈ old.toList, GridRow.Valid r)
    (hnew : ∀ r ∈ new.toList, GridRow.Valid r) :
    (indices.map (modelGramContribution old new)).sum ≤
      ((indices.map fun i => roundUpStageOne (gramContribution old new i)).sum : ℤ) /
        (100000000 : ℝ) := by
  have hdiv (ns : List ℕ) :
      (ns.map fun i => (roundUpStageOne (gramContribution old new i) : ℝ) / 100000000).sum =
        ((ns.map fun i => roundUpStageOne (gramContribution old new i)).sum : ℤ) / (100000000 : ℝ) := by
    induction ns with
    | nil => simp
    | cons i is ih => simp [ih, add_div]
  rw [← hdiv]
  apply List.sum_le_sum
  intro i _
  rw [← gramContribution_cast old new hold hnew]
  exact_mod_cast roundUpStageOne_sound (gramContribution old new i)

/-- Each accepted linear block gives an upper bound for its real Gram sum. -/
theorem stageOneLinearBlockCheck_sound (range : ℕ × ℕ) (value : ℤ)
    (h : stageOneLinearBlockCheck range value = true) :
    ((List.range' range.1 (min range.2 stageOneLinearGrid.size - range.1)).map
      (modelGramContribution stageOneQuadraticGrid stageOneLinearGrid)).sum ≤
        (value : ℝ) / 100000000 := by
  simp only [stageOneLinearBlockCheck, decide_eq_true_eq] at h
  rw [← h, stageOneLinearBlock, linearBlock_eq_rangeSum]
  exact modelGramBlock_upper _ _ _
    (fun _ hr => prepareRows_valid stageOneQuadratic_validWidths hr)
    (fun _ hr => prepareRows_valid stageOneLinear_validWidths hr)

/-- The accepted quadratic block bounds its real lower-triangular Gram sum. -/
theorem stageOneQuadraticBlockCheck_sound (value : ℤ)
    (h : stageOneQuadraticBlockCheck value = true) :
    ((List.range' 0 stageOneQuadraticGrid.size).map
      (modelGramContribution #[] stageOneQuadraticGrid)).sum ≤
        (value : ℝ) / 100000000 := by
  simp only [stageOneQuadraticBlockCheck, decide_eq_true_eq] at h
  rw [← h, stageOneQuadraticBlock, quadraticBlock_eq_rangeSum, min_self, Nat.sub_zero]
  exact modelGramBlock_upper _ _ _ (fun _ hr => by simp at hr)
    (fun _ hr => prepareRows_valid stageOneQuadratic_validWidths hr)

end Chowla.Checker

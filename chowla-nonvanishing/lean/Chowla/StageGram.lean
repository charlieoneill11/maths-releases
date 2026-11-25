import Chowla.CheckerStages
import Init.Data.Range.Lemmas

namespace Chowla.Checker

open scoped BigOperators

/-- A symmetric Gram square has one diagonal contribution and two contributions
for each entry strictly below the diagonal. -/
theorem sum_symmetric_triangle (n : ℕ) (g : ℕ → ℕ → ℝ) (hs : ∀ i j, g i j = g j i) :
    (∑ i ∈ Finset.range n, (g i i + 2 * ∑ j ∈ Finset.range i, g i j)) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, g i j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
    have h : (∑ i ∈ Finset.range n, g i n) = ∑ i ∈ Finset.range n, g n i := by
      exact Finset.sum_congr rfl (fun i _ => hs i n)
    rw [h]
    ring

private theorem foldl_sum {α β : Type*} [AddCommMonoid β] (xs : List α) (f : α → β)
    (a : β) : xs.foldl (fun b x => b + f x) a = a + (xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc]

theorem loop_sum {R : Type*} [AddCommMonoid R] (start stop : ℕ) (f : ℕ → R) :
    (Id.run do
      let mut acc : R := 0
      for j in [start:stop] do
        acc := acc + f j
      return acc) = ((List.range' start (stop - start)).map f).sum := by
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, foldl_sum]

theorem normRow_eq_sum (rows : Array GridRow) (i : Fin rows.size) (r : GridRow) :
    normRow rows i.val r =
      gramGrid r rows[i] +
        2 * ∑ j ∈ Finset.range i.val, (rows[j]?.map (gramGrid r)).getD 0 := by
  have hmin : min (i.val + 1) rows.size = i.val + 1 := min_eq_left i.isLt
  let f := fun j : ℕ =>
    match rows[j]? with
    | some c => (if j = i.val then 1 else 2) * gramGrid r c
    | none => 0
  have hs : normRow rows i.val r = ((List.range (i.val + 1)).map f).sum := by
    have hf := loop_sum 0 (i.val + 1) f
    rw [Nat.sub_zero, ← List.range_eq_range'] at hf
    rw [← hf]
    unfold normRow
    simp only [hmin]
    congr 1
    apply congrArg Id.run
    congr 1
    congr 1
    funext j a
    cases he : rows[j]? <;> simp [f, he]
  rw [hs]
  have hf : ((List.range (i.val + 1)).map f).sum = ∑ j ∈ Finset.range (i.val + 1), f j := by
    rw [← List.toFinset_range]
    exact (List.sum_toFinset f List.nodup_range).symm
  rw [hf, Finset.sum_range_succ]
  have hdiag : f i.val = gramGrid r rows[i] := by
    simp [f, i.isLt]
  rw [hdiag, Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < i.val := Finset.mem_range.mp hj
  simp [f, hj'.trans i.isLt, ne_of_lt hj']

private theorem array_sum {α R : Type*} [AddCommMonoid R] (rows : Array α) (f : α → R) :
    (rows.toList.map f).sum = ∑ j ∈ Finset.range rows.size, (rows[j]?.map f).getD 0 := by
  let g := fun j : ℕ => (rows[j]?.map f).getD 0
  calc
    (rows.toList.map f).sum = ∑ j : Fin rows.toList.length, f (rows.toList.get j) := by
      rw [← List.sum_ofFn (f := fun j : Fin rows.toList.length => f (rows.toList.get j))]
      change _ = (List.ofFn (f ∘ rows.toList.get)).sum
      rw [← List.map_ofFn, List.ofFn_get]
    _ = ∑ j : Fin rows.toList.length, g j.val := by
      apply Finset.sum_congr rfl
      intro j _
      have hj : j.val < rows.size := by exact j.isLt
      simp [g, hj, Array.getElem_toList hj]
    _ = _ := by rw [Fin.sum_univ_eq_sum_range]; simp [g]

theorem crossRow_eq_sum (r : GridRow) (rows : Array GridRow) :
    crossRow r rows =
      2 * ∑ j ∈ Finset.range rows.size, (rows[j]?.map (gramGrid r)).getD 0 := by
  simp [crossRow, ← Array.foldl_toList, foldl_sum, array_sum]

theorem normRow_cast (rows : Array GridRow) (i : Fin rows.size) (r : GridRow) :
    (normRow rows i.val r : ℝ) =
      (gramGrid r rows[i] : ℝ) +
        2 * ∑ j ∈ Finset.range i.val, ((rows[j]?.map (gramGrid r)).getD 0 : ℝ) := by
  rw [normRow_eq_sum]
  push_cast
  rfl


def gramContribution (old new : Array GridRow) (i : ℕ) : ℚ :=
  match new[i]? with
  | some r => crossRow r old + normRow new i r
  | none => 0

private theorem gramIncrease_eq_sum (old new : Array GridRow) :
    gramIncrease old new = ∑ i ∈ Finset.range new.size, gramContribution old new i := by
  let f := gramContribution old new
  have hloop := loop_sum 0 new.size f
  rw [Nat.sub_zero, ← List.range_eq_range'] at hloop
  have hfold : gramIncrease old new = ((List.range new.size).map f).sum := by
    rw [← hloop]
    unfold gramIncrease
    congr 1
    apply congrArg Id.run
    congr 2
    funext i a
    cases hd : new[i]? <;> simp [f, gramContribution, hd, add_assoc]
  rw [hfold, ← List.toFinset_range]
  exact (List.sum_toFinset f List.nodup_range).symm

/-- The cast of a computed Gram increase is the corresponding model increase, once
each computed pair has been identified with the corresponding model row product. -/
theorem gramIncrease_sound (old new : Array GridRow)
    (model : GridRow → Row)
    (cross : ∀ i : Fin new.size, ∀ j : Fin old.size,
      (gramGrid new[i] old[j] : ℝ) = innerRow (model new[i]) (model old[j]))
    (within : ∀ i j : Fin new.size,
      (gramGrid new[i] new[j] : ℝ) = innerRow (model new[i]) (model new[j])) :
    (gramIncrease old new : ℝ) =
      2 * inner (old.toList.map model) (new.toList.map model) +
        inner (new.toList.map model) (new.toList.map model) := by
  let g := fun i j : ℕ =>
    ((new[i]?.map fun a => (new[j]?.map fun b => innerRow (model a) (model b)).getD 0)).getD 0
  let h := fun i j : ℕ =>
    ((new[i]?.map fun a => (old[j]?.map fun b => innerRow (model a) (model b)).getD 0)).getD 0
  let f := gramContribution old new
  rw [gramIncrease_eq_sum]
  change ((∑ i ∈ Finset.range new.size, f i : ℚ) : ℝ) = _
  push_cast
  have hg : ∀ i j, g i j = g j i := by
    intro i j
    cases hi : new[i]? <;> cases hj : new[j]? <;> simp [g, hi, hj, innerRow_comm]
  have htri := sum_symmetric_triangle new.size g hg
  have hloopEq : (∑ i ∈ Finset.range new.size, (f i : ℝ)) =
      ∑ i ∈ Finset.range new.size,
        (2 * (∑ j ∈ Finset.range old.size, h i j) +
          (g i i + 2 * ∑ j ∈ Finset.range i, g i j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    let ii : Fin new.size := ⟨i, hi'⟩
    simp only [f, gramContribution, Array.getElem?_eq_getElem hi']
    rw [Rat.cast_add, crossRow_eq_sum]
    push_cast
    rw [normRow_cast new ii new[i]]
    have d : (gramGrid new[i] new[ii] : ℝ) = g i i := by
      exact (within ii ii).trans (by simp [g, hi', ii])
    have a : (∑ j ∈ Finset.range old.size, ((old[j]?.map (gramGrid new[i])).getD 0 : ℝ)) =
        ∑ j ∈ Finset.range old.size, h i j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      simpa [h, hi', hj'] using cross ii ⟨j, hj'⟩
    have b : (∑ j ∈ Finset.range i, ((new[j]?.map (gramGrid new[i])).getD 0 : ℝ)) =
        ∑ j ∈ Finset.range i, g i j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := (Finset.mem_range.mp hj).trans hi'
      simpa [g, hi', hj'] using within ii ⟨j, hj'⟩
    simp only [d, ii, a, b]
  have hinner (A B : Array GridRow) :
      inner (A.toList.map model) (B.toList.map model) =
        ∑ i ∈ Finset.range A.size, ∑ j ∈ Finset.range B.size,
          ((A[i]?.map fun a => (B[j]?.map fun b => innerRow (model a) (model b)).getD 0)).getD 0 := by
    unfold inner
    simp only [List.map_map, Function.comp_def]
    rw [array_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [Array.getElem?_eq_getElem hi', Option.map_some, Option.getD_some]
    rw [array_sum]
  rw [hloopEq, Finset.sum_add_distrib, ← Finset.mul_sum, htri,
    inner_comm (old.toList.map model), hinner, hinner]

theorem roundUpStageOne_zero : roundUpStageOne 0 = 0 := by decide +kernel

private theorem roundedLinearBlock_eq_sum (linear quadratic : Array GridRow) :
    roundedLinearBlock linear quadratic 0 linear.size =
      ∑ i ∈ Finset.range linear.size, roundUpStageOne (gramContribution quadratic linear i) := by
  let f := fun i => roundUpStageOne (gramContribution quadratic linear i)
  have hl := loop_sum 0 linear.size f
  rw [Nat.sub_zero, ← List.range_eq_range'] at hl
  have hs : roundedLinearBlock linear quadratic 0 linear.size =
      ((List.range linear.size).map f).sum := by
    rw [← hl]
    unfold roundedLinearBlock
    simp only [min_self]
    congr 1
    apply congrArg Id.run
    congr 2
    funext i a
    cases h : linear[i]? <;> simp [f, gramContribution, h, add_comm, roundUpStageOne_zero]
  rw [hs, ← List.toFinset_range]
  exact (List.sum_toFinset f List.nodup_range).symm

private theorem roundedQuadraticBlock_eq_sum (rows : Array GridRow) :
    roundedQuadraticBlock rows 0 rows.size =
      ∑ i ∈ Finset.range rows.size, roundUpStageOne (gramContribution #[] rows i) := by
  let f := fun i => roundUpStageOne (gramContribution #[] rows i)
  have hl := loop_sum 0 rows.size f
  rw [Nat.sub_zero, ← List.range_eq_range'] at hl
  have hs : roundedQuadraticBlock rows 0 rows.size = ((List.range rows.size).map f).sum := by
    rw [← hl]
    unfold roundedQuadraticBlock
    simp only [min_self]
    congr 1
    apply congrArg Id.run
    congr 2
    funext i a
    cases h : rows[i]? <;> simp [f, gramContribution, h, crossRow, roundUpStageOne_zero]
  rw [hs, ← List.toFinset_range]
  exact (List.sum_toFinset f List.nodup_range).symm

/-- Rounding each paper group upward encloses the total unrounded Gram square. -/
theorem stageOne_rounding_upper (linear quadratic : Array GridRow) :
    gramIncrease quadratic linear + gramIncrease #[] quadratic ≤
      ((roundedLinearBlock linear quadratic 0 linear.size +
        roundedQuadraticBlock quadratic 0 quadratic.size : ℤ) : ℚ) / 100000000 := by
  rw [gramIncrease_eq_sum, gramIncrease_eq_sum, roundedLinearBlock_eq_sum,
    roundedQuadraticBlock_eq_sum, Int.cast_add, add_div]
  push_cast
  simp only [Finset.sum_div]
  apply add_le_add <;> exact Finset.sum_le_sum (fun _ _ => roundUpStageOne_sound _)

end Chowla.Checker

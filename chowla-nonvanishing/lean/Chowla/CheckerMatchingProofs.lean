import Chowla.CheckerMultiplicity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith

namespace Chowla.Checker

open scoped BigOperators

private theorem eraseEach_fst (xs : List ℚ) : (eraseEach xs).map Prod.fst = xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simpa [eraseEach, List.map_map, Function.comp_def] using congrArg (a :: ·) ih

private theorem eraseEach_mem_width {xs : List ℚ} {choice : ℚ × List ℚ}
    (h : choice ∈ eraseEach xs) : choice.1 ∈ xs := by
  rw [← eraseEach_fst xs]
  exact List.mem_map.mpr ⟨choice, h, rfl⟩

private theorem eraseEach_remaining {xs : List ℚ} (hxs : xs.Pairwise (· ≤ ·))
    {choice : ℚ × List ℚ} (h : choice ∈ eraseEach xs) :
    choice.2 = xs.erase choice.1 := by
  induction xs generalizing choice with
  | nil => simp [eraseEach] at h
  | cons a as ih =>
    rcases List.pairwise_cons.mp hxs with ⟨hhead, htail⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact (List.erase_cons_head a as).symm
    · obtain ⟨⟨b, rest⟩, hb, rfl⟩ := List.mem_map.mp h
      have herase := @ih htail (b, rest) hb
      change a :: rest = (a :: as).erase b
      change rest = as.erase b at herase
      rw [herase]
      by_cases heq : a = b
      · subst b
        have hmem : a ∈ as := eraseEach_mem_width hb
        cases as with
        | nil => simp at hmem
        | cons c cs =>
          have hac : a ≤ c := hhead c (by simp)
          have hca : c ≤ a := by
            rcases List.mem_cons.mp hmem with h | h
            · exact h.symm.le
            · exact (List.pairwise_cons.mp htail).1 a h
          have he : c = a := le_antisymm hca hac
          subst c
          simp
      · rw [List.erase_cons_tail (by simpa using heq)]

/-- Summing over distinct entries with their exact multiplicity equals summing
over the labelled list. -/
theorem dedup_count_sum (xs : List ℚ) (f : ℚ → ℚ) :
    (xs.dedup.map (fun x => (xs.count x : ℚ) * f x)).sum = (xs.map f).sum := by
  have hd : xs.dedup.toFinset = xs.toFinset := by ext x; simp
  rw [← List.sum_toFinset _ (List.nodup_dedup xs), hd]
  simpa only [nsmul_eq_mul] using (Finset.sum_list_map_count xs f).symm

/-- On sorted widths, deleting any one of several equal entries gives the same
remaining list. Grouping by width therefore preserves the exact labelled sum. -/
theorem eraseEach_count_sum (xs : List ℚ) (hxs : xs.Pairwise (· ≤ ·))
    (f : ℚ × List ℚ → ℚ) :
    (xs.dedup.map (fun a => (xs.count a : ℚ) * f (a, xs.erase a))).sum =
      ((eraseEach xs).map f).sum := by
  rw [dedup_count_sum]
  calc
    _ = (((eraseEach xs).map Prod.fst).map (fun a => f (a, xs.erase a))).sum := by
      rw [eraseEach_fst]
    _ = _ := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro c hc
      change f (c.1, xs.erase c.1) = f c
      rw [← eraseEach_remaining hxs hc]

private theorem weightedSum_collect_matching_step (a : MatchingWeight) (weights : List MatchingWeight)
    (f : List ℚ → ℚ) :
    weightedSum (collectMatchingWeight a weights) f = a.2 * f a.1 + weightedSum weights f := by
  cases weights with
  | nil => rfl
  | cons b bs =>
    change weightedSum
      (if a.1 = b.1 then (a.1, a.2 + b.2) :: bs else a :: b :: bs) f = _
    by_cases h : a.1 = b.1
    · rw [if_pos h]
      simp only [weightedSum_cons, h]
      ring
    · rw [if_neg h, weightedSum_cons]

private theorem weightedSum_collect_matching (weights : List MatchingWeight) (f : List ℚ → ℚ) :
    weightedSum (collectMatchingWeights weights) f = weightedSum weights f := by
  let cmp := fun a b : MatchingWeight => !(b.1.lex a.1 (fun x y => x < y))
  have hfold (xs : List MatchingWeight) :
      weightedSum (xs.foldr collectMatchingWeight []) f = weightedSum xs f := by
    induction xs with
    | nil => rfl
    | cons a as ih =>
      rw [List.foldr_cons, weightedSum_collect_matching_step, ih, weightedSum_cons]
  change weightedSum ((weights.mergeSort cmp).foldr collectMatchingWeight []) f = _
  rw [hfold]
  exact weightedSum_perm (List.mergeSort_perm _ _) f

private theorem weightedSum_unmatched (weights : List MatchingWeight) (a : ℚ) (f : List ℚ → ℚ) :
    weightedSum (weights.map fun (rest, weight) => (insertWidth a rest, weight)) f =
      weightedSum weights (fun rest => f (insertWidth a rest)) := by
  simp [weightedSum, Function.comp_def]

private theorem weightedSum_paired (weights : List MatchingWeight) (k : ℚ) (f : List ℚ → ℚ) :
    weightedSum (weights.map fun (rest, weight) => (rest, k * weight)) f =
      k * weightedSum weights f := by
  simp [weightedSum, Function.comp_def, mul_assoc, List.sum_map_mul_left]

private theorem weightedSum_flatMap {α : Type} (s : List α) (choices : α → List MatchingWeight)
    (f : List ℚ → ℚ) :
    weightedSum (s.flatMap choices) f = (s.map fun a => weightedSum (choices a) f).sum := by
  induction s with
  | nil => rfl
  | cons a as ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons, weightedSum_append, ih]

/-- The implemented compression preserves every weighted sum of labelled partial matchings. -/
theorem matchingWeights_sound (left right : List ℚ) (hsorted : right.Pairwise (· ≤ ·))
    (f : List ℚ → ℚ) :
    weightedSum (matchingWeights left right) f =
      weightedSum (labelledMatchingWeights left right) f := by
  induction left generalizing right f with
  | nil => rfl
  | cons a left ih =>
    simp only [matchingWeights, labelledMatchingWeights, weightedSum_collect_matching,
      weightedSum_append, weightedSum_unmatched, weightedSum_flatMap, weightedSum_paired]
    rw [ih right hsorted (fun rest => f (insertWidth a rest))]
    congr 1
    calc
      _ = (right.dedup.map fun b =>
          (right.count b : ℚ) * (pairWeight a b *
            weightedSum (labelledMatchingWeights left (right.erase b)) f)).sum := by
        congr 1
        apply List.map_congr_left
        intro b _
        rw [ih (right.erase b) (hsorted.erase b) f, mul_assoc]
      _ = _ := eraseEach_count_sum right hsorted
        (fun (b, remaining) => pairWeight a b *
          weightedSum (labelledMatchingWeights left remaining) f)

theorem eraseEach_sum {widths : List ℚ} {choice : ℚ × List ℚ}
    (h : choice ∈ eraseEach widths) : choice.1 + choice.2.sum = widths.sum := by
  induction widths generalizing choice with
  | nil => simp [eraseEach] at h
  | cons a widths ih =>
    rcases List.mem_cons.mp h with rfl | h
    · rfl
    · obtain ⟨⟨b, bs⟩, hb, rfl⟩ := List.mem_map.mp h
      have hs := ih hb
      change b + (a + bs.sum) = a + widths.sum
      change b + bs.sum = widths.sum at hs
      linarith

private theorem rectangleTail_eq_zero_of_sum {widths : List ℚ} (h : widths.sum ≤ 1) :
    rectangleTail widths = 0 := by simp [rectangleTail, h]

/-- The exceptional-block calculation sums once over each labelled choice of an
additional variable in the marked block. -/
theorem contractionTerm_expansion (B : Primitive) (widths : List ℚ)
    (hsorted : widths.Pairwise (· ≤ ·)) (hwidths : ∀ a ∈ widths, 0 ≤ a) :
    contractionTerm B widths =
      markedCumulant B widths + rectangleTail widths * mean B +
        ((eraseEach widths).map (fun (a, rest) => rectangleTail rest * covariance B a)).sum := by
  unfold contractionTerm
  by_cases h : widths.sum ≤ 1
  · rw [if_pos h, rectangleTail_eq_zero_of_sum h, zero_mul, add_zero]
    have hzero : (eraseEach widths).map (fun (a, rest) => rectangleTail rest * covariance B a) =
        (eraseEach widths).map (fun _ => (0 : ℚ)) := by
      apply List.map_congr_left
      intro choice hchoice
      have hs := eraseEach_sum hchoice
      have ha := hwidths choice.1 (eraseEach_mem_width hchoice)
      have hsum : choice.2.sum ≤ 1 := by linarith
      change rectangleTail choice.2 * covariance B choice.1 = 0
      simp [rectangleTail_eq_zero_of_sum hsum]
    rw [hzero, List.sum_map_zero, add_zero]
  · rw [if_neg h]
    congr 1
    calc
      _ = (widths.dedup.map fun a => (widths.count a : ℚ) *
          (rectangleTail (widths.erase a) * covariance B a)).sum := by
        congr 1
        apply List.map_congr_left
        intro a _
        by_cases hz : rectangleTail (widths.erase a) = 0
        · simp [hz]
        · simp [hz, mul_assoc]
      _ = _ := eraseEach_count_sum widths hsorted
        (fun (a, rest) => rectangleTail rest * covariance B a)

private theorem foldl_weightedSum (weights : List MatchingWeight) (f : List ℚ → ℚ)
    (total : ℚ) :
    weights.foldl (fun acc (rest, c) => acc + c * f rest) total =
      total + weightedSum weights f := by
  induction weights generalizing total with
  | nil => simp [weightedSum]
  | cons h ts ih =>
    rw [List.foldl_cons, ih, weightedSum_cons]
    exact add_assoc ..

/-- The compressed contraction is the weighted sum over the labelled partial matching recursion. -/
theorem contraction_labelled (B : Primitive) (left right : List ℚ) :
    let R := right.mergeSort (fun a b => a ≤ b)
    contraction B left right =
      weightedSum (labelledMatchingWeights left R) (contractionTerm B) := by
  let R := right.mergeSort (fun a b => a ≤ b)
  have hR : R.Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) right
  change (matchingWeights left R).foldl _ (0 : ℚ) = _
  rw [foldl_weightedSum, zero_add, matchingWeights_sound left R hR]

end Chowla.Checker

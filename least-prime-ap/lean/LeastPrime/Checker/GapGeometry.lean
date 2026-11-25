import LeastPrime.Checker.Grid
import Mathlib.Data.List.OfFn

/-! The length of the revealed part and its reflection on a level-two gap. -/

namespace LeastPrime.Checker

open Function MeasureTheory Set
open scoped BigOperators

noncomputable section

private theorem grid_mono : Monotone grid := fun _ _ h => grid_le_iff.mpr h

private theorem grid_sum (L : List ℕ) : grid L.sum = (L.map grid).sum := by
  induction L with
  | nil => simp
  | cons n L ih => simp [grid_add, ih]

private theorem sum_map_eq_sum_get {α M : Type*} [AddCommMonoid M]
    (L : List α) (f : α → M) : (L.map f).sum = ∑ i : Fin L.length, f (L.get i) := by
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

private theorem denote_eq_iUnion (T : GridSet) :
    denote T = ⋃ i : Fin T.length, interval (T.get i) := by
  ext x
  simp only [mem_denote, mem_iUnion]
  exact List.exists_mem_iff_get

private theorem descending_intervals_pairwise {T : GridSet}
    (hT : T.Pairwise fun I J => J.2 < I.1) :
    Pairwise (Disjoint on fun i : Fin T.length => interval (T.get i)) := by
  intro i j hij
  have hd := disjointIntervals_of_descending hT
  rcases lt_or_gt_of_ne hij with h | h
  · exact List.pairwise_iff_get.mp hd i j h
  · exact (List.pairwise_iff_get.mp hd j i h).symm

private def shiftedInterval (r : ℝ) (I : GridInterval) : Set ℝ :=
  Icc (r - grid I.2) (r - grid I.1)

private theorem shiftedInterval_eq_image (r : ℝ) (I : GridInterval) :
    shiftedInterval r I = (fun w : ℝ => r - w) '' interval I := by
  ext x
  change x ∈ Icc _ _ ↔ x ∈ (fun w : ℝ => r - w) '' interval I
  constructor
  · intro hx
    exact ⟨r - x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, by ring⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨by linarith [hy.2], by linarith [hy.1]⟩

private theorem image_denote_eq_iUnion (T : GridSet) (r : ℝ) :
    (fun w : ℝ => r - w) '' denote T = ⋃ i : Fin T.length, shiftedInterval r (T.get i) := by
  rw [denote_eq_iUnion, Set.image_iUnion]
  simp only [shiftedInterval_eq_image]

private theorem shifted_intervals_pairwise {T : GridSet} (r : ℝ)
    (hT : T.Pairwise fun I J => J.2 < I.1) :
    Pairwise (Disjoint on fun i : Fin T.length => shiftedInterval r (T.get i)) := by
  intro i j hij
  change Disjoint (shiftedInterval r (T.get i)) (shiftedInterval r (T.get j))
  rw [shiftedInterval_eq_image, shiftedInterval_eq_image]
  exact Set.disjoint_image_of_injective (fun a b h => by linarith) (descending_intervals_pairwise hT hij)

private theorem volume_shifted_denote_eq_grid_length {T : GridSet} (r : ℝ)
    (hT : ∀ I ∈ T, Good I) (hsep : T.Pairwise fun I J => J.2 < I.1) :
    volume.real ((fun w : ℝ => r - w) '' denote T) = grid (targetLength T) := by
  rw [image_denote_eq_iUnion, measureReal_iUnion_fintype (shifted_intervals_pairwise r hsep)
    (fun _ => measurableSet_Icc) (fun _ => isCompact_Icc.measure_ne_top)]
  rw [targetLength, grid_sum, List.map_map, sum_map_eq_sum_get]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := (hT _ (List.get_mem T i)).1
  have heq : r - grid (T.get i).1 - (r - grid (T.get i).2) =
      grid (T.get i).2 - grid (T.get i).1 := by ring
  simp only [shiftedInterval, Real.volume_real_Icc, heq, Function.comp_apply, width, grid_sub hi,
    max_eq_left (sub_nonneg.mpr (grid_le_iff.mpr hi))]

private def overlapWidth (r : ℝ) (I J : GridInterval) : ℝ :=
  max (min (grid I.2) (r - grid J.1) - max (grid I.1) (r - grid J.2)) 0

private theorem volume_inter_shiftedInterval (r : ℝ) (I J : GridInterval) :
    volume.real (interval I ∩ shiftedInterval r J) = overlapWidth r I J := by
  rw [interval, shiftedInterval, Icc_inter_Icc, Real.volume_real_Icc]
  rfl

private theorem overlapWidth_at_grid {r : ℕ} {I J : GridInterval}
    (hJ : J.1 ≤ J.2) (hr : J.2 ≤ r) : overlapWidth (grid r) I J = grid (reflectedOverlap r I J) := by
  unfold overlapWidth reflectedOverlap
  rw [← grid_sub (hJ.trans hr), ← grid_sub hr, ← grid_mono.map_min, ← grid_mono.map_max]
  let top := min I.2 (r - J.1)
  let bot := max I.1 (r - J.2)
  change max (grid top - grid bot) 0 = grid (top - bot)
  by_cases h : bot ≤ top
  · rw [grid_sub h, max_eq_left (sub_nonneg.mpr (grid_le_iff.mpr h))]
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge h), grid_zero,
      max_eq_right (sub_nonpos.mpr (grid_le_iff.mpr (le_of_not_ge h)))]

private theorem intersection_eq_iUnion (T : GridSet) (r : ℝ) :
    denote T ∩ (fun w : ℝ => r - w) '' denote T =
      ⋃ ij : Fin T.length × Fin T.length, interval (T.get ij.1) ∩ shiftedInterval r (T.get ij.2) := by
  rw [denote_eq_iUnion (T := T), Set.image_iUnion]
  simp only [← shiftedInterval_eq_image]
  ext x
  simp only [mem_inter_iff, mem_iUnion, Prod.exists]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨i, j, hi, hj⟩
  · rintro ⟨i, j, hi, hj⟩
    exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩

private theorem intersection_families_disjoint {T : GridSet} (r : ℝ)
    (hsep : T.Pairwise fun I J => J.2 < I.1) :
    Pairwise (Disjoint on fun ij : Fin T.length × Fin T.length =>
      interval (T.get ij.1) ∩ shiftedInterval r (T.get ij.2)) := by
  intro i j hij
  change Disjoint (interval (T.get i.1) ∩ shiftedInterval r (T.get i.2))
    (interval (T.get j.1) ∩ shiftedInterval r (T.get j.2))
  by_cases h : i.1 = j.1
  · have h' : i.2 ≠ j.2 := fun hh => hij (Prod.ext h hh)
    exact (shifted_intervals_pairwise r hsep h').mono inter_subset_right inter_subset_right
  · exact (descending_intervals_pairwise hsep h).mono inter_subset_left inter_subset_left

private theorem volume_intersection_eq_sum {T : GridSet} (r : ℝ)
    (hsep : T.Pairwise fun I J => J.2 < I.1) :
    volume.real (denote T ∩ (fun w : ℝ => r - w) '' denote T) =
      ∑ i : Fin T.length, ∑ j : Fin T.length, overlapWidth r (T.get i) (T.get j) := by
  rw [intersection_eq_iUnion, measureReal_iUnion_fintype (intersection_families_disjoint r hsep)
    (fun _ => measurableSet_Icc.inter measurableSet_Icc)
    (fun _ => measure_ne_top_of_subset inter_subset_left isCompact_Icc.measure_ne_top)]
  simp only [Fintype.sum_prod_type, volume_inter_shiftedInterval]

private theorem gLower_eq_sum {T : GridSet} (r : ℝ) (hT : ∀ I ∈ T, Good I)
    (hsep : T.Pairwise fun I J => J.2 < I.1) :
    gLower r (denote T) = 2 * grid (targetLength T) -
      ∑ i : Fin T.length, ∑ j : Fin T.length, overlapWidth r (T.get i) (T.get j) := by
  have hK : IsCompact (denote T) := by
    rw [denote_eq_iUnion]
    exact isCompact_iUnion fun _ => isCompact_Icc
  have hKR : IsCompact ((fun w : ℝ => r - w) '' denote T) :=
    hK.image (continuous_const.sub continuous_id)
  have h := measureReal_union_add_inter (μ := volume) hKR.measurableSet hK.measure_ne_top
    hKR.measure_ne_top
  rw [volume_denote hT (disjointIntervals_of_descending hsep),
    volume_shifted_denote_eq_grid_length r hT hsep,
    volume_intersection_eq_sum r hsep] at h
  unfold gLower
  linarith

private theorem overlap_sum_at_grid {T : GridSet} (r : ℕ) (hT : ∀ I ∈ T, Good I)
    (hr : ∀ I ∈ T, I.2 ≤ r) :
    (∑ i : Fin T.length, ∑ j : Fin T.length, overlapWidth (grid r) (T.get i) (T.get j)) =
      grid ((T.map fun I => (T.map (reflectedOverlap r I)).sum).sum) := by
  rw [grid_sum, List.map_map, sum_map_eq_sum_get]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Function.comp_apply, grid_sum, List.map_map, sum_map_eq_sum_get]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact overlapWidth_at_grid (hT _ (List.get_mem T j)).1 (hr _ (List.get_mem T j))

/-- The lower level-two evaluator returns the union length at grid points. -/
theorem grid_availableLength_lower {T : GridSet} {r : ℕ} (hT : ∀ I ∈ T, Good I)
    (hsep : T.Pairwise fun I J => J.2 < I.1) (hr : ∀ I ∈ T, I.2 ≤ r) :
    grid (availableLength .lower T r) = gLower (grid r) (denote T) := by
  rw [gLower_eq_sum _ hT hsep, overlap_sum_at_grid r hT hr]
  generalize hO : (T.map fun I => (T.map (reflectedOverlap r I)).sum).sum = O
  have hnonneg : 0 ≤ gLower (grid r) (denote T) := measureReal_nonneg
  rw [gLower_eq_sum _ hT hsep, overlap_sum_at_grid r hT hr, hO] at hnonneg
  have hle : O ≤ 2 * targetLength T := by
    apply grid_le_iff.mp
    rw [show 2 * targetLength T = targetLength T + targetLength T by omega, grid_add]
    linarith
  cases T with
  | nil => simp [availableLength, targetLength] at hO ⊢; simp [hO.symm]
  | cons I T =>
    unfold availableLength
    rw [hO, grid_sub hle]
    rw [show 2 * targetLength (I :: T) = targetLength (I :: T) + targetLength (I :: T) by omega,
      grid_add]
    ring

private theorem extrema_denote {head : GridInterval} {tail : GridSet}
    (hT : ∀ I ∈ head :: tail, Good I) (hsep : (head :: tail).Pairwise fun I J => J.2 < I.1) :
    IsLeast (denote (head :: tail)) (grid ((head :: tail).getLastD head).1) ∧
    IsGreatest (denote (head :: tail)) (grid head.2) := by
  have hhead : head ∈ head :: tail := List.mem_cons_self
  have hlast : ((head :: tail).getLastD head) ∈ head :: tail := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast (by simp)]
    exact List.getLast_mem _
  constructor
  · refine ⟨mem_denote.mpr ⟨_, hlast, le_rfl, grid_le_iff.mpr (hT _ hlast).1⟩, ?_⟩
    intro x hx
    obtain ⟨I, hI, hIx⟩ := mem_denote.mp hx
    have hsep' : (head :: tail).Pairwise fun (I J : GridInterval) => J.1 ≤ I.1 :=
      hsep.imp_of_mem (fun _ hJ h => (hT _ hJ).1.trans h.le)
    have hlI : ((head :: tail).getLastD head).1 ≤ I.1 := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast (by simp)]
      exact hsep'.rel_getLast_of_rel_getLast_getLast hI le_rfl
    exact (grid_le_iff.mpr hlI).trans hIx.1
  · refine ⟨mem_denote.mpr ⟨head, hhead, grid_le_iff.mpr (hT _ hhead).1, le_rfl⟩, ?_⟩
    intro x hx
    obtain ⟨I, hI, hIx⟩ := mem_denote.mp hx
    apply hIx.2.trans
    apply grid_le_iff.mpr
    rcases List.mem_cons.mp hI with rfl | hI
    · exact le_rfl
    · exact ((List.pairwise_cons.mp hsep).1 _ hI).le.trans (hT _ hhead).1

private theorem gUpper_eq_max {head : GridInterval} {tail : GridSet} (r : ℝ)
    (hT : ∀ I ∈ head :: tail, Good I) (hsep : (head :: tail).Pairwise fun I J => J.2 < I.1) :
    gUpper r (denote (head :: tail)) =
      max (r - grid ((head :: tail).getLastD head).1) (grid head.2) := by
  obtain ⟨hmin, hmax⟩ := extrema_denote hT hsep
  rw [gUpper, if_pos ⟨_, hmin.1⟩, hmin.csInf_eq, hmax.csSup_eq]

/-- The upper level-two evaluator returns the maximum length at grid points. -/
theorem grid_availableLength_upper {T : GridSet} {r : ℕ} (hT : ∀ I ∈ T, Good I)
    (hsep : T.Pairwise fun I J => J.2 < I.1) (hr : ∀ I ∈ T, I.2 ≤ r) :
    grid (availableLength .upper T r) = gUpper (grid r) (denote T) := by
  cases T with
  | nil => simp [availableLength, denote, gUpper]
  | cons I T =>
    have hlast : (I :: T).getLastD I ∈ I :: T := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast (by simp)]
      exact List.getLast_mem _
    rw [gUpper_eq_max _ hT hsep]
    unfold availableLength
    rw [grid_mono.map_max, grid_sub ((hT _ hlast).1.trans (hr _ hlast))]

private theorem le_left_or_right_le {a b x : ℝ} (h : x ∉ Ioo a b) : x ≤ a ∨ b ≤ x := by
  by_cases hx : x ≤ a
  · exact Or.inl hx
  · exact Or.inr (le_of_not_gt fun hb => h ⟨lt_of_not_ge hx, hb⟩)

private theorem overlapWidth_affine {a b : ℝ} {I J : GridInterval}
    (hI : I.1 ≤ I.2) (hJ : J.1 ≤ J.2)
    (hcuts : ∀ c ∈ [I.1 + J.1, I.1 + J.2, I.2 + J.1, I.2 + J.2], grid c ∉ Ioo a b) :
    ∃ α β : ℝ, ∀ r ∈ Icc a b, overlapWidth r I J = α * r + β := by
  have hmin : grid I.2 + grid J.1 ∉ Ioo a b := by
    rw [← grid_add]
    exact hcuts _ (by simp)
  have hmax : grid I.1 + grid J.2 ∉ Ioo a b := by
    rw [← grid_add]
    exact hcuts _ (by simp)
  rcases le_left_or_right_le hmin with hmin | hmin
  · rcases le_left_or_right_le hmax with hmax | hmax
    · have hcut : grid I.2 + grid J.2 ∉ Ioo a b := by
        rw [← grid_add]
        exact hcuts _ (by simp)
      rcases le_left_or_right_le hcut with hz | hz
      · refine ⟨0, 0, fun r hr => ?_⟩
        unfold overlapWidth
        rw [min_eq_left (by linarith [hr.1, hmin]), max_eq_right (show grid I.1 ≤ r - grid J.2 by linarith [hr.1, hmax]),
          max_eq_right (by linarith [hr.1, hz])]
        ring
      · refine ⟨-1, grid I.2 + grid J.2, fun r hr => ?_⟩
        unfold overlapWidth
        rw [min_eq_left (by linarith [hr.1, hmin]), max_eq_right (show grid I.1 ≤ r - grid J.2 by linarith [hr.1, hmax]),
          max_eq_left (by linarith [hr.2, hz])]
        ring
    · refine ⟨0, grid I.2 - grid I.1, fun r hr => ?_⟩
      unfold overlapWidth
      rw [min_eq_left (by linarith [hr.1, hmin]), max_eq_left (show r - grid J.2 ≤ grid I.1 by linarith [hr.2, hmax]),
        max_eq_left (sub_nonneg.mpr (grid_le_iff.mpr hI))]
      ring
  · rcases le_left_or_right_le hmax with hmax | hmax
    · refine ⟨0, grid J.2 - grid J.1, fun r hr => ?_⟩
      have h := grid_le_iff.mpr hJ
      unfold overlapWidth
      rw [min_eq_right (by linarith [hr.2, hmin]), max_eq_right (show grid I.1 ≤ r - grid J.2 by linarith [hr.1, hmax]),
        max_eq_left (by linarith)]
      ring
    · have hcut : grid I.1 + grid J.1 ∉ Ioo a b := by
        rw [← grid_add]
        exact hcuts _ (by simp)
      rcases le_left_or_right_le hcut with hz | hz
      · refine ⟨1, -(grid I.1 + grid J.1), fun r hr => ?_⟩
        unfold overlapWidth
        rw [min_eq_right (by linarith [hr.2, hmin]), max_eq_left (show r - grid J.2 ≤ grid I.1 by linarith [hr.2, hmax]),
          max_eq_left (by linarith [hr.1, hz])]
        ring
      · refine ⟨0, 0, fun r hr => ?_⟩
        unfold overlapWidth
        rw [min_eq_right (by linarith [hr.2, hmin]), max_eq_left (show r - grid J.2 ≤ grid I.1 by linarith [hr.2, hmax]),
          max_eq_right (by linarith [hr.2, hz])]
        ring

private theorem mem_breakpointCandidates_lower {T : GridSet} {I J : GridInterval}
    (hi : I ∈ T) (hj : J ∈ T) {c : ℕ}
    (hc : c ∈ [I.1 + J.1, I.1 + J.2, I.2 + J.1, I.2 + J.2]) :
    c ∈ breakpointCandidates .lower T := by
  cases T with
  | nil => simp at hi
  | cons k T =>
    simp only [breakpointCandidates, List.mem_flatMap]
    exact ⟨I, hi, J, hj, hc⟩

private theorem grid_not_mem_Ioo {a b c : ℕ} (h : ¬ (a < c ∧ c < b)) :
    grid c ∉ Ioo (grid a) (grid b) := by
  intro hc
  exact h ⟨grid_lt_iff.mp hc.1, grid_lt_iff.mp hc.2⟩

/-- The reflected-union length is affine between consecutive level-two breakpoints. -/
theorem gLower_affine_between_cuts {T : GridSet} {a b : ℕ} (hT : ∀ I ∈ T, Good I)
    (hsep : T.Pairwise fun I J => J.2 < I.1)
    (hc : ∀ c ∈ breakpointCandidates .lower T, ¬ (a < c ∧ c < b)) :
    ∃ α β : ℝ, ∀ r ∈ Icc (grid a) (grid b), gLower r (denote T) = α * r + β := by
  classical
  have hPiece (i j : Fin T.length) := overlapWidth_affine
    (hT _ (List.get_mem T i)).1 (hT _ (List.get_mem T j)).1
    (fun _ hx => grid_not_mem_Ioo (hc _ (mem_breakpointCandidates_lower
      (List.get_mem T i) (List.get_mem T j) hx)))
  choose α β hEq using hPiece
  refine ⟨-(∑ i, ∑ j, α i j), 2 * grid (targetLength T) - ∑ i, ∑ j, β i j, ?_⟩
  intro r hr
  rw [gLower_eq_sum r hT hsep]
  simp_rw [hEq _ _ r hr, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

/-- The maximum available length is affine between its level-two breakpoints. -/
theorem gUpper_affine_between_cuts {T : GridSet} {a b : ℕ} (hT : ∀ I ∈ T, Good I)
    (hsep : T.Pairwise fun I J => J.2 < I.1)
    (hc : ∀ c ∈ breakpointCandidates .upper T, ¬ (a < c ∧ c < b)) :
    ∃ α β : ℝ, ∀ r ∈ Icc (grid a) (grid b), gUpper r (denote T) = α * r + β := by
  cases T with
  | nil => exact ⟨0, 0, fun _ _ => by simp [denote, gUpper]⟩
  | cons I T =>
    let l := grid ((I :: T).getLastD I).1
    let u := grid I.2
    have hcut : l + u ∉ Ioo (grid a) (grid b) := by
      dsimp [l, u]
      rw [← grid_add]
      exact grid_not_mem_Ioo (hc _ (by simp [breakpointCandidates]))
    rcases le_left_or_right_le hcut with h | h
    · refine ⟨1, -l, fun r hr => ?_⟩
      rw [gUpper_eq_max r hT hsep]
      change max (r - l) u = _
      rw [max_eq_left (by linarith [hr.1, h])]
      ring
    · refine ⟨0, u, fun r hr => ?_⟩
      rw [gUpper_eq_max r hT hsep]
      change max (r - l) u = _
      rw [max_eq_right (by linarith [hr.2, h])]
      ring

end

end LeastPrime.Checker

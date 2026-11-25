import Chowla.CheckerPartitionBridge
import Chowla.CheckerContraction
import Chowla.Model.RectangleTail

namespace Chowla.Checker

open scoped BigOperators

variable {ι : Type} [DecidableEq ι]

/-- Sort the width list of a finite labelled set. Individual labels remain counted even
when several widths are equal. -/
noncomputable def sortedWidths (width : ι → ℚ) (U : Finset ι) : List ℚ :=
  (U.toList.map width).mergeSort (· ≤ ·)

private theorem insertWidth_eq (a : ℚ) (xs : List ℚ) :
    insertWidth a xs = List.orderedInsert (· ≤ ·) a xs := by
  induction xs with
  | nil => rfl
  | cons b rest ih =>
    simp only [insertWidth, List.orderedInsert_cons, ih]

private theorem sortedWidths_insert (width : ι → ℚ) (U : Finset ι) {i : ι} (hi : i ∉ U) :
    sortedWidths width (insert i U) = insertWidth (width i) (sortedWidths width U) := by
  rw [insertWidth_eq]
  have hperm : (sortedWidths width (insert i U)).Perm (width i :: sortedWidths width U) :=
    (List.mergeSort_perm ((insert i U).toList.map width) _).trans
      (((Finset.toList_insert hi).map width).trans
        ((List.mergeSort_perm (U.toList.map width) _).symm.cons (width i)))
  apply (hperm.trans (List.perm_orderedInsert (· ≤ ·) (width i) _).symm).eq_of_pairwise' (r := fun a b : ℚ => a ≤ b)
  · exact List.pairwise_mergeSort' (· ≤ ·) _
  · exact (List.pairwise_mergeSort' (· ≤ ·) _).orderedInsert (width i) _

private theorem sortedWidths_toFinset (width : ι → ℚ) (r : List ι) (hr : r.Nodup)
    (horder : (r.map width).Pairwise (· ≤ ·)) : sortedWidths width r.toFinset = r.map width := by
  have hp : (r.toFinset.toList).Perm r := List.perm_of_nodup_nodup_toFinset_eq
    (Finset.nodup_toList _) hr (by simp)
  have hperm : (sortedWidths width r.toFinset).Perm (r.map width) :=
    (List.mergeSort_perm (r.toFinset.toList.map width) (· ≤ ·)).trans (hp.map width)
  exact hperm.eq_of_pairwise' (r := fun a b : ℚ => a ≤ b)
    (List.pairwise_mergeSort' (· ≤ ·) _) horder

private theorem labels_erase_finset (r : List ι) (hr : r.Nodup) (j : ι) :
    (r.erase j).toFinset = r.toFinset.erase j := by
  ext a
  simp [hr.mem_erase_iff]

omit [DecidableEq ι] in
private theorem eraseEach_map (width : ι → ℚ) (r : List ι) :
    eraseEach (r.map width) =
      (eraseEach r).map (fun (j, rest) => (width j, rest.map width)) := by
  induction r with
  | nil => rfl
  | cons j rest ih =>
    simp only [List.map_cons, eraseEach, List.map_map, ih]
    rfl

omit [DecidableEq ι] in
private theorem eraseEach_label_fst (r : List ι) : (eraseEach r).map Prod.fst = r := by
  induction r with
  | nil => rfl
  | cons a rest ih =>
    simpa [eraseEach, List.map_map, Function.comp_def] using congrArg (a :: ·) ih

private theorem eraseEach_label_rest {r : List ι} (hr : r.Nodup)
    {choice : ι × List ι} (h : choice ∈ eraseEach r) :
    choice.2 = r.erase choice.1 := by
  induction r generalizing choice with
  | nil => simp [eraseEach] at h
  | cons a rest ih =>
    rcases List.nodup_cons.mp hr with ⟨hN, hrest⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact (List.erase_cons_head a rest).symm
    · obtain ⟨⟨b, rs⟩, hb, rfl⟩ := List.mem_map.mp h
      have hm : b ∈ rest := by
        rw [← eraseEach_label_fst rest]
        exact List.mem_map.mpr ⟨(b, rs), hb, rfl⟩
      have hab : a ≠ b := fun e => hN (e.symm ▸ hm)
      have he : rs = rest.erase b := ih hrest hb
      change a :: rs = (a :: rest).erase b
      rw [he, List.erase_cons_tail (by simpa using hab)]

/-- Weighted matching sum using the exact rational weights as real scalars. -/
noncomputable def realWeighted (rows : List MatchingWeight) (f : List ℚ → ℝ) : ℝ :=
  (rows.map fun (rest, q) => (q : ℝ) * f rest).sum

private theorem realWeighted_append (p q : List MatchingWeight) (f : List ℚ → ℝ) :
    realWeighted (p ++ q) f = realWeighted p f + realWeighted q f := by
  simp [realWeighted]

private theorem realWeighted_unmatched (p : List MatchingWeight) (a : ℚ) (f : List ℚ → ℝ) :
    realWeighted (p.map fun (rest, weight) => (insertWidth a rest, weight)) f =
      realWeighted p (fun rest => f (insertWidth a rest)) := by
  simp [realWeighted, Function.comp_def]

private theorem realWeighted_paired (p : List MatchingWeight) (w : ℚ) (f : List ℚ → ℝ) :
    realWeighted (p.map fun (rest, weight) => (rest, w * weight)) f =
      (w : ℝ) * realWeighted p f := by
  simp [realWeighted, Function.comp_def, Rat.cast_mul, mul_assoc, List.sum_map_mul_left]

private theorem realWeighted_flatMap {α : Type} (s : List α) (g : α → List MatchingWeight)
    (f : List ℚ → ℝ) :
    realWeighted (s.flatMap g) f = (s.map fun a => realWeighted (g a) f).sum := by
  induction s with
  | nil => rfl
  | cons a as ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons, realWeighted_append, ih]

/-- The partition-based and recursive interpretations of a labelled partial matching. -/
theorem labelledMatchingWeights_partition (width : ι → ℚ) (L : Finset ι) (l r : List ι)
    (hl : l.Nodup) (hr : r.Nodup) (hL : ∀ i ∈ l, i ∈ L) (hR : Disjoint r.toFinset L)
    (horder : (r.map width).Pairwise (· ≤ ·)) (f : List ℚ → ℝ) :
    realWeighted (labelledMatchingWeights (l.map width) (r.map width)) f =
      supportWeighted (crossBlockWeight L (fun i j => (pairWeight (width i) (width j) : ℝ)))
        (fun U => f (sortedWidths width U)) ((l ++ r).toFinset) := by
  classical
  let mark := fun i j => (pairWeight (width i) (width j) : ℝ)
  let G := crossBlockWeight L mark
  induction l generalizing r f with
  | nil =>
    simp only [List.map_nil, labelledMatchingWeights, realWeighted, List.map_cons, List.sum_cons,
      List.sum_nil, Rat.cast_one, one_mul, add_zero, List.nil_append]
    rw [supportWeighted_cross_right L mark _ r.toFinset hR, sortedWidths_toFinset width r hr horder]
  | cons i l ih =>
    let U := ((i :: l) ++ r).toFinset
    let V := (l ++ r).toFinset
    have hiU : i ∈ U := by simp [U]
    have hiL : i ∈ L := hL i (by simp)
    obtain ⟨hiN, hlN⟩ := List.nodup_cons.mp hl
    have hiR : i ∉ r.toFinset := fun h => Finset.disjoint_left.mp hR h hiL
    have hiV : i ∉ V := by simp [V, hiN, hiR]
    have hUErase : U.erase i = V := by
      simp only [U, List.cons_append, List.toFinset_cons]
      exact Finset.erase_insert hiV
    have hRight : U \ L = r.toFinset := by
      ext j
      constructor
      · intro hj
        obtain ⟨hju, hjl⟩ := Finset.mem_sdiff.mp hj
        have hlr : j ∈ (i :: l) ++ r := List.mem_toFinset.mp hju
        rcases List.mem_append.mp hlr with h | h
        · exact (hjl (hL j h)).elim
        · exact List.mem_toFinset.mpr h
      · intro hj
        exact Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_toFinset.mp hj)),
          Finset.disjoint_left.mp hR hj⟩
    have htail : ∀ j ∈ l, j ∈ L := fun j hj => hL j (by simp [hj])
    change _ = supportWeighted G _ U
    rw [supportWeighted_cross_left L mark _ U i hiU hiL, hUErase, hRight]
    simp only [List.map_cons, labelledMatchingWeights, realWeighted_append, realWeighted_unmatched,
      realWeighted_flatMap, realWeighted_paired, eraseEach_map width r, List.map_map]
    congr 1
    · rw [ih r hlN hr htail hR horder]
      apply supportWeighted_congr_test G V
      intro S hS
      have hiS : i ∉ S := fun h => hiV (hS h)
      rw [sortedWidths_insert width S hiS]
    · have hmap :
        ((eraseEach r).map ((fun (b, remaining) =>
          (pairWeight (width i) b : ℝ) * realWeighted (labelledMatchingWeights (l.map width) remaining) f)
          ∘ fun (j, rest) => (width j, rest.map width))).sum =
        (r.map fun j => mark i j *
          realWeighted (labelledMatchingWeights (l.map width) ((r.erase j).map width)) f).sum := by
        calc
          _ = ((eraseEach r).map (fun q => mark i q.1 *
              realWeighted (labelledMatchingWeights (l.map width) ((r.erase q.1).map width)) f)).sum := by
            congr 1
            apply List.map_congr_left
            intro q hq
            rcases q with ⟨j, ls⟩
            have he := eraseEach_label_rest hr hq
            change ls = r.erase j at he
            simp [mark, he]
          _ = _ := by
            let H := fun j => mark i j *
              realWeighted (labelledMatchingWeights (l.map width) ((r.erase j).map width)) f
            change ((eraseEach r).map (H ∘ Prod.fst)).sum = (r.map H).sum
            rw [← List.map_map, eraseEach_label_fst]
      rw [hmap, ← List.sum_toFinset _ hr]
      apply Finset.sum_congr rfl
      intro j hj
      have hjr := List.mem_toFinset.mp hj
      have hjL : j ∉ L := Finset.disjoint_left.mp hR hj
      have hjl : j ∉ l := fun hm => hjL (htail j hm)
      have hiNe : i ≠ j := fun e => hjL (e ▸ hiL)
      have hjdomain : U \ {i, j} = (l ++ r.erase j).toFinset := by
        ext a
        simp only [U, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
          List.mem_toFinset, List.cons_append, List.mem_cons, List.mem_append, hr.mem_erase_iff]
        by_cases hai : a = i
        · subst a
          simp [hiN, show i ∉ r from fun h => hiR (List.mem_toFinset.mpr h)]
        by_cases haj : a = j
        · subst a
          simp [hjl]
        simp [hai, haj]
      have hR' : Disjoint (r.erase j).toFinset L := hR.mono_left (by rw [labels_erase_finset r hr j]; exact Finset.erase_subset _ _)
      have horder' : ((r.erase j).map width).Pairwise (· ≤ ·) :=
        horder.sublist ((List.erase_sublist (l := r) (a := j)).map width)
      rw [ih (r.erase j) hlN (hr.erase j) htail hR' horder' f, hjdomain]


private noncomputable def sortedLabels (width : ι → ℚ) (U : Finset ι) : List ι :=
  U.toList.mergeSort (fun i j => width i ≤ width j)

private theorem sortedLabels_toFinset (width : ι → ℚ) (U : Finset ι) :
    (sortedLabels width U).toFinset = U := by
  ext i
  have h := List.mergeSort_perm U.toList (fun i j => width i ≤ width j)
  simpa only [List.mem_toFinset, sortedLabels, Finset.mem_toList] using h.mem_iff (a := i)

omit [DecidableEq ι] in
private theorem sortedLabels_nodup (width : ι → ℚ) (U : Finset ι) :
    (sortedLabels width U).Nodup :=
  ((List.mergeSort_perm U.toList _).nodup_iff).mpr (Finset.nodup_toList U)

omit [DecidableEq ι] in
private theorem sortedLabels_widthOrder (width : ι → ℚ) (U : Finset ι) :
    ((sortedLabels width U).map width).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  have htrans (i j k : ι) : decide (width i ≤ width j) = true →
      decide (width j ≤ width k) = true → decide (width i ≤ width k) = true := by
    simp only [decide_eq_true_eq]
    exact le_trans
  have htotal (i j : ι) : (decide (width i ≤ width j) || decide (width j ≤ width i)) = true := by
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total (width i) (width j)
  simpa only [sortedLabels, decide_eq_true_eq] using List.pairwise_mergeSort htrans htotal U.toList

private theorem sortedLabels_widths (width : ι → ℚ) (U : Finset ι) :
    (sortedLabels width U).map width = sortedWidths width U := by
  symm
  rw [← sortedWidths_toFinset width (sortedLabels width U)
      (sortedLabels_nodup width U) (sortedLabels_widthOrder width U), sortedLabels_toFinset]

private theorem sortedWidths_perm (width : ι → ℚ) (U : Finset ι) (ls : List ι)
    (hn : ls.Nodup) (hU : ls.toFinset = U) :
    (sortedWidths width U).Perm (ls.map width) := by
  apply (List.mergeSort_perm (U.toList.map width) _).trans
  apply List.Perm.map
  exact List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList U) hn (by simpa using hU.symm)

/-- Sorting right widths before the recursive calculation is a reordering of
the same right labels. -/
theorem labelledMatchingWeights_partition_sort (width : ι → ℚ) (L : Finset ι) (l r : List ι)
    (hl : l.Nodup) (hr : r.Nodup) (hL : ∀ i ∈ l, i ∈ L) (hR : Disjoint r.toFinset L)
    (f : List ℚ → ℝ) :
    realWeighted (labelledMatchingWeights (l.map width) ((r.map width).mergeSort (· ≤ ·))) f =
      supportWeighted (crossBlockWeight L (fun i j => (pairWeight (width i) (width j) : ℝ)))
        (fun U => f (sortedWidths width U)) ((l ++ r).toFinset) := by
  have hmem : Disjoint (sortedLabels width r.toFinset).toFinset L := by
    rwa [sortedLabels_toFinset]
  have hsort : (sortedLabels width r.toFinset).map width = (r.map width).mergeSort (· ≤ ·) := by
    rw [sortedLabels_widths]
    exact ((sortedWidths_perm width r.toFinset r hr rfl).trans
      (List.mergeSort_perm (r.map width) (· ≤ ·)).symm).eq_of_pairwise'
      (r := fun a b : ℚ => a ≤ b)
      (List.pairwise_mergeSort' (· ≤ ·) _) (List.pairwise_mergeSort' (· ≤ ·) _)
  have h := labelledMatchingWeights_partition width L l (sortedLabels width r.toFinset) hl
    (sortedLabels_nodup width r.toFinset) hL hmem (sortedLabels_widthOrder width r.toFinset) f
  rw [hsort, List.toFinset_append, sortedLabels_toFinset, ← List.toFinset_append] at h
  exact h

private theorem rectangleTail_perm {A B : List ℝ} (hAB : A.Perm B) : Chowla.rectangleTail A = Chowla.rectangleTail B := by
  unfold Chowla.rectangleTail
  rw [← hAB.length_eq]
  by_cases hn : 2 ≤ A.length
  · rw [if_pos hn, if_pos hn]
    exact delta_perm (hAB.map rectangle) (by
      intro η hη
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hη
      exact rectangle_isProfile t)
  · rw [if_neg hn, if_neg hn]

/-- Interpret the rational contraction term once for each unmatched label,
while retaining the order used in the mathematical partition formula. -/
theorem contractionTerm_finset {κ : Type} [LinearOrder κ] (p : Spline)
    (width : κ → ℚ) (U : Finset κ) (hp : IsProfile p.toReal)
    (hwidth : ∀ i ∈ U, (width i : ℝ) ∈ Set.Ioc 0 1) :
    (contractionTerm (splinePrimitives p) (sortedWidths width U) : ℝ) =
      cumulant (p.toReal :: (widthsOn (fun i => (width i : ℝ)) U).map rectangle) +
        Chowla.rectangleTail (widthsOn (fun i => (width i : ℝ)) U) * cumulant [p.toReal] +
        ∑ i ∈ U, Chowla.rectangleTail (widthsOn (fun j => (width j : ℝ)) (U.erase i)) *
          cumulant [p.toReal, rectangle (width i : ℝ)] := by
  classical
  have hall : ∀ a ∈ sortedWidths width U, (a : ℝ) ∈ Set.Ioc 0 1 := by
    intro a ha
    rw [← sortedLabels_widths] at ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact hwidth i ((sortedLabels_toFinset width U) ▸ List.mem_toFinset.mpr hi)
  have hs : (sortedWidths width U).Pairwise (· ≤ ·) := List.pairwise_mergeSort' (· ≤ ·) _
  rw [contractionTerm_sound p (sortedWidths width U) hp hs hall]
  let w := fun i => (width i : ℝ)
  have widthOrder (S : Finset κ) :
      ((sortedWidths width S).map (fun a : ℚ => (a : ℝ))).Perm (widthsOn w S) := by
    simpa [widthsOn, w, List.map_map, Function.comp_def] using
      (sortedWidths_perm width S (S.sort (· ≤ ·)) (S.sort_nodup _) (S.sort_toFinset _)).map
        (fun a : ℚ => (a : ℝ))
  have hmark : cumulant (p.toReal :: ((sortedWidths width U).map (fun a : ℚ => (a : ℝ))).map rectangle) =
      cumulant (p.toReal :: (widthsOn w U).map rectangle) := by
    apply cumulant_perm (((widthOrder U).map rectangle).cons _)
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
      exact rectangle_isProfile a
  rw [hmark, rectangleTail_perm (widthOrder U)]
  congr 1
  let H := fun i => Chowla.rectangleTail (widthsOn w (U.erase i)) *
    cumulant [p.toReal, rectangle (width i : ℝ)]
  have hindex : ((eraseEach (sortedLabels width U)).map (H ∘ Prod.fst)).sum = ∑ i ∈ U, H i := by
    rw [← List.map_map, eraseEach_label_fst, ← List.sum_toFinset _ (sortedLabels_nodup width U),
      sortedLabels_toFinset]
  change _ = ∑ i ∈ U, H i
  rw [← hindex, ← sortedLabels_widths width U, eraseEach_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  let i := c.1
  have herase : c.2.toFinset = U.erase i := by
    rw [eraseEach_label_rest (sortedLabels_nodup width U) hc, labels_erase_finset,
      sortedLabels_toFinset]
    exact sortedLabels_nodup width U
  have hperm : ((c.2.map width).map (fun a : ℚ => (a : ℝ))).Perm (widthsOn w (U.erase i)) := by
    have hcsub : c.2.Sublist (sortedLabels width U) :=
      eraseEach_label_rest (sortedLabels_nodup width U) hc ▸ List.erase_sublist
    have h := sortedWidths_perm width (U.erase i) c.2
      ((sortedLabels_nodup width U).sublist hcsub) herase
    exact (h.map (fun a : ℚ => (a : ℝ))).symm.trans (widthOrder _)
  rcases c with ⟨i, ls⟩
  exact congrArg (fun u => u * cumulant [p.toReal, rectangle (width i : ℝ)])
    (rectangleTail_perm hperm)

end Chowla.Checker

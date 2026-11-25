import Chowla.Model.RectangleTail

namespace Chowla

open scoped BigOperators

/-- Shift width labels by one to make room for the distinguished profile. -/
noncomputable def withMarkedLabel (h : FourierProfile) (C : List ℝ) :
    Fin C.length ↪ Fin (h :: C.map rectangle).length where
  toFun i := ⟨i.val + 1, by simp⟩
  inj' i j hij := Fin.ext (Nat.succ.inj (congrArg Fin.val hij))

noncomputable def markedLabel (h : FourierProfile) (C : List ℝ) :
    Fin (h :: C.map rectangle).length := ⟨0, List.length_cons .. ▸ Nat.zero_lt_succ _⟩

@[simp] theorem withMarkedLabel_val (h : FourierProfile) (C : List ℝ) (i : Fin C.length) :
    (withMarkedLabel h C i).val = i.val + 1 := rfl

@[simp] theorem markedLabel_val (h : FourierProfile) (C : List ℝ) :
    (markedLabel h C).val = 0 := rfl

theorem withMarkedLabel_strictMono (h : FourierProfile) (C : List ℝ) :
    StrictMono (withMarkedLabel h C) := by
  intro i j hij
  exact Nat.succ_lt_succ hij

@[simp] theorem markedLabel_notMem_map (h : FourierProfile) (C : List ℝ)
    (T : Finset (Fin C.length)) : markedLabel h C ∉ T.map (withMarkedLabel h C) := by
  rintro hi
  obtain ⟨i, hi, he⟩ := Finset.mem_map.mp hi
  have hz : i.val + 1 = 0 := congrArg (fun j : Fin (h :: C.map rectangle).length => j.val) he
  omega

theorem map_widthLabels_univ (h : FourierProfile) (C : List ℝ) :
    Finset.univ.map (withMarkedLabel h C) = Finset.univ.erase (markedLabel h C) := by
  ext i
  constructor
  · intro hi
    exact Finset.mem_erase.mpr ⟨fun he => markedLabel_notMem_map h C _ (he ▸ hi), Finset.mem_univ _⟩
  · intro hi
    have hne := (Finset.mem_erase.mp hi).1
    have h0 : i.val ≠ 0 := fun he => hne (Fin.ext he)
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have hlt := i.isLt
    simp only [List.length_cons, List.length_map, hj, Nat.succ_lt_succ_iff] at hlt
    exact Finset.mem_map.mpr ⟨⟨j, hlt⟩, Finset.mem_univ _, Fin.ext hj.symm⟩

noncomputable def markedWidth (h : FourierProfile) (C : List ℝ) (i : Fin (h :: C.map rectangle).length) : ℝ :=
  (0 :: C).get (Fin.cast (by simp) i)

@[simp] theorem markedWidth_shift (h : FourierProfile) (C : List ℝ) (i : Fin C.length) :
    markedWidth h C (withMarkedLabel h C i) = C.get i := by
  simp only [markedWidth, List.get_eq_getElem, Fin.val_cast, withMarkedLabel_val, List.getElem_cons_succ]

@[simp] theorem get_withMarkedLabel (h : FourierProfile) (C : List ℝ) (i : Fin C.length) :
    (h :: C.map rectangle).get (withMarkedLabel h C i) = rectangle (C.get i) := by
  simp only [List.get_eq_getElem, withMarkedLabel_val, List.getElem_cons_succ, List.getElem_map]

theorem widthsOn_map_marked (h : FourierProfile) (C : List ℝ) (T : Finset (Fin C.length)) :
    widthsOn (markedWidth h C) (T.map (withMarkedLabel h C)) = widthsOn C.get T := by
  unfold widthsOn
  rw [← StrictMonoOn.map_finsetSort (f := withMarkedLabel h C) T ((withMarkedLabel_strictMono h C).strictMonoOn (↑T : Set (Fin C.length))), List.map_map]
  apply List.map_congr_left
  intro i _
  exact markedWidth_shift h C i

theorem profilesOn_map_marked (h : FourierProfile) (C : List ℝ) (T : Finset (Fin C.length)) :
    (((T.map (withMarkedLabel h C)).sort (· ≤ ·)).map (h :: C.map rectangle).get) =
      (widthsOn C.get T).map rectangle := by
  unfold widthsOn
  rw [← StrictMonoOn.map_finsetSort (f := withMarkedLabel h C) T ((withMarkedLabel_strictMono h C).strictMonoOn (↑T : Set (Fin C.length))), List.map_map, List.map_map]
  apply List.map_congr_left
  intro i _
  exact get_withMarkedLabel h C i

theorem blockCumulant_insert_marked (h : FourierProfile) (C : List ℝ) (T : Finset (Fin C.length)) :
    blockCumulant (h :: C.map rectangle).get (insert (markedLabel h C) (T.map (withMarkedLabel h C))) =
      cumulant (h :: (widthsOn C.get T).map rectangle) := by
  have hm (i : Fin (h :: C.map rectangle).length) (_ : i ∈ T.map (withMarkedLabel h C)) :
      markedLabel h C ≤ i := Nat.zero_le _
  rw [blockCumulant, Finset.sort_insert (· ≤ ·) hm (markedLabel_notMem_map h C T),
    List.map_cons, profilesOn_map_marked]
  rfl

/-- A block of labelled rectangles supported entirely in one row has tail equal to zero. -/
theorem rectangleTail_eq_zero_of_one_row (A B : List ℝ)
    (hA : WidthsAdmissible A) (hB : WidthsAdmissible B) (T : Finset (Fin (A ++ B).length))
    (hT : (∀ i ∈ T, i.val < A.length) ∨ (∀ i ∈ T, A.length ≤ i.val)) :
    rectangleTail (widthsOn (A ++ B).get T) = 0 := by
  have hnonneg (i : Fin (A ++ B).length) (_ : i ∈ T) : 0 ≤ (A ++ B).get i := by
    have hmem := List.get_mem (A ++ B) i
    exact (List.mem_append.mp hmem).elim (fun ha => (hA.1 _ ha).1.le) (fun hb => (hB.1 _ hb).1.le)
  apply rectangleTail_eq_zero_of_sum (nonneg_mem_widthsOn hnonneg)
  rw [sum_widthsOn]
  rcases hT with hl | hr
  · let e : Fin A.length ↪ Fin (A ++ B).length :=
      ⟨fun i => ⟨i.val, by
        simpa only [List.length_append] using (i.isLt.trans_le (Nat.le_add_right A.length B.length))⟩,
        fun _ _ he => Fin.ext (congrArg (fun k : Fin (A ++ B).length => k.val) he)⟩
    have hsub : T ⊆ Finset.univ.map e := fun i hi =>
      Finset.mem_map.mpr ⟨⟨i.val, hl i hi⟩, Finset.mem_univ _, Fin.ext rfl⟩
    have hne (i : Fin (A ++ B).length) (hi : i ∈ Finset.univ.map e) (_ : i ∉ T) :
        0 ≤ (A ++ B).get i := by
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact (hA.1 _ (List.get_mem A j)).1.le.trans_eq
        (List.getElem_append_left j.isLt).symm
    apply (Finset.sum_le_sum_of_subset_of_nonneg hsub hne).trans
    rw [Finset.sum_map]
    have he (i : Fin A.length) : (A ++ B).get (e i) = A.get i := List.getElem_append_left i.isLt
    simp_rw [he, ← List.sum_ofFn, List.ofFn_get]
    exact hA.2
  · let e : Fin B.length ↪ Fin (A ++ B).length :=
      ⟨fun i => ⟨A.length + i.val, by
        simpa only [List.length_append] using (Nat.add_lt_add_left i.isLt A.length)⟩,
        fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))⟩
    have hsub : T ⊆ Finset.univ.map e := by
      intro i hi
      have hlt := i.isLt
      simp only [List.length_append] at hlt
      have hir := hr i hi
      refine Finset.mem_map.mpr ⟨⟨i.val - A.length, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
      change A.length + (i.val - A.length) = i.val
      exact Nat.add_sub_of_le (hr i hi)
    have he (i : Fin B.length) : (A ++ B).get (e i) = B.get i := by
      change (A ++ B)[A.length + i.val] = B[i.val]
      rw [List.getElem_append_right (Nat.le_add_right _ _)]
      simp
    have hne (i : Fin (A ++ B).length) (hi : i ∈ Finset.univ.map e) (_ : i ∉ T) :
        0 ≤ (A ++ B).get i := by
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact (hB.1 _ (List.get_mem B j)).1.le.trans_eq (he j).symm
    apply (Finset.sum_le_sum_of_subset_of_nonneg hsub hne).trans
    rw [Finset.sum_map]
    simp_rw [he, ← List.sum_ofFn, List.ofFn_get]
    exact hB.2

end Chowla

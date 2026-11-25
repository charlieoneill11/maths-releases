import Chowla.Model.WickLabels
import Chowla.Model.Rows
import Chowla.EnclosureProofs

namespace Chowla

open MeasureTheory Set
open scoped BigOperators Topology

def WidthsAdmissible (A : List ℝ) : Prop :=
  (∀ a ∈ A, a ∈ Ioo (0 : ℝ) 1) ∧ A.sum ≤ 1

theorem delta_rectangles_eq_zero_of_sum (A : List ℝ) (hA : ∀ a ∈ A, 0 ≤ a) (hs : A.sum ≤ 1) :
    delta (A.map rectangle) = 0 := by
  apply delta_eq_zero_of_support _ A
  · intro _ hf
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hf
    exact rectangle_isProfile a
  · clear hs
    induction A with
    | nil => exact .nil
    | cons a A ih =>
      exact .cons (rectangle_hasRadiusAtMost (hA a List.mem_cons_self))
        (ih fun b hb => hA b (List.mem_cons_of_mem a hb))
  · exact hs

theorem cumulant_eq_delta_of_length {hs : List FourierProfile} (h : 3 ≤ hs.length) :
    cumulant hs = delta hs := by
  rcases hs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> simp_all [cumulant]

private theorem sum_sort_map {n : ℕ} (T : Finset (Fin n)) (w : Fin n → ℝ) :
    ((T.sort (· ≤ ·)).map w).sum = ∑ i ∈ T, w i := by
  rw [← List.sum_toFinset w (T.sort_nodup (· ≤ ·))]
  simp

/-- Lemma 24. An unmarked block surviving centering and Wick subtraction must meet both
rows, since a block contained in either row has total radius at most one. -/
theorem connected_partitions_of_profile (h : FourierProfile) (A B : List ℝ)
    (hh : IsProfile h) (hA : WidthsAdmissible A) (hB : WidthsAdmissible B) :
    modelExpectation (stat h * wick (A.map rectangle) * wick (B.map rectangle)) =
      partitionSum (h :: (A ++ B).map rectangle) (fun T =>
        (∃ i ∈ T, i.val = 0) ∨
          ((∃ i ∈ T, 0 < i.val ∧ i.val ≤ A.length) ∧
            (∃ i ∈ T, A.length < i.val))) := by
  classical
  let fs := h :: (A ++ B).map rectangle
  let n := fs.length
  have hn : n = A.length + B.length + 1 := by simp [n, fs]
  let L := leftLabels n A.length
  let R := rightLabels n A.length
  let keep := KeepWickPartition L R
  let connected : Finset (Fin n) → Prop := fun T =>
    (∃ i ∈ T, i.val = 0) ∨ ((∃ i ∈ T, i ∈ L) ∧ (∃ i ∈ T, i ∈ R))
  have hp := wick_moment_partition_eq h (A.map rectangle) (B.map rectangle) (by
    intro t ht
    rcases List.mem_cons.mp ht with he | ht
    · exact he ▸ hh
    · rw [← List.map_append] at ht
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp ht
      exact rectangle_isProfile a)
  simp only [List.length_map] at hp
  have hp' : modelExpectation (stat h * wick (A.map rectangle) * wick (B.map rectangle)) =
      partitionSum fs keep := by
    refine hp.trans ?_
    exact congrArg (fun ls : List FourierProfile => partitionSum (h :: ls)
      (KeepWickPartition (leftLabels (h :: ls).length A.length)
        (rightLabels (h :: ls).length A.length))) (List.map_append ..).symm
  have heConn : (fun T : Finset (Fin n) =>
      (∃ i ∈ T, i.val = 0) ∨
        ((∃ i ∈ T, 0 < i.val ∧ i.val ≤ A.length) ∧
          (∃ i ∈ T, A.length < i.val))) = connected := by
    funext T
    apply propext
    simp [connected, L, R, leftLabels, rightLabels]
  rw [hp', heConn]
  let q := 0 :: (A ++ B)
  have hlen : n = q.length := by simp [n, fs, q]
  let w (i : Fin n) : ℝ := q.get (Fin.cast hlen i)
  have zero_or_lr (i : Fin n) : i.val = 0 ∨ i ∈ L ∨ i ∈ R := by
    simp only [L, R, leftLabels, rightLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hL0 (i : Fin n) (hi : i ∈ L) : i.val ≠ 0 := by
    exact Nat.ne_of_gt (Finset.mem_filter.mp hi).2.1
  have hR0 (i : Fin n) (hi : i ∈ R) : i.val ≠ 0 := by
    have hr := (Finset.mem_filter.mp hi).2
    omega
  have hrect (i : Fin n) (hi : i.val ≠ 0) : fs.get i = rectangle (w i) := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hi
    simp only [fs, q, w, List.get_eq_getElem, Fin.val_cast, hj, List.getElem_cons_succ, List.getElem_map]
  have hw0 (i : Fin n) : 0 ≤ w i := by
    have hm := List.get_mem q (Fin.cast hlen i)
    rcases List.mem_cons.mp hm with he | ha
    · exact he.ge
    · rcases List.mem_append.mp ha with hA' | hB'
      · exact (hA.1 _ hA').1.le
      · exact (hB.1 _ hB').1.le
  have hsumL : (∑ i ∈ L, w i) = A.sum := by
    change (∑ i ∈ leftLabels n A.length, w i) = A.sum
    rw [← map_leftEmbedding A.length B.length n hn, Finset.sum_map]
    have he (i : Fin A.length) : w (leftEmbedding A.length B.length n hn i) = A.get i := by
      have hi := i.isLt
      change (0 :: (A ++ B))[i.val + 1]'(by simp; omega) = A[i.val]
      rw [List.getElem_cons_succ, List.getElem_append_left i.isLt]
    simp_rw [he]
    rw [← List.sum_ofFn, List.ofFn_get]
  have hsumR : (∑ i ∈ R, w i) = B.sum := by
    change (∑ i ∈ rightLabels n A.length, w i) = B.sum
    rw [← map_rightEmbedding A.length B.length n hn, Finset.sum_map]
    have he (i : Fin B.length) : w (rightEmbedding A.length B.length n hn i) = B.get i := by
      have hi := i.isLt
      change (0 :: (A ++ B))[A.length + i.val + 1]'(by simp) = B[i.val]
      rw [List.getElem_cons_succ, List.getElem_append_right (by omega)]
      congr 1
      omega
    simp_rw [he]
    rw [← List.sum_ofFn, List.ofFn_get]
  have hmixed (T : Finset (Fin n)) (hT : connected T) : keep T := by
    have hdis := disjoint_label_sets n A.length
    refine ⟨?_, ?_⟩
    · rintro ⟨i, hi, rfl⟩
      rcases hT with ⟨j, hj, hzero⟩ | ⟨⟨j, hj, hLj⟩, k, hk, hRk⟩
      · have hz : i.val = 0 := by rwa [Finset.mem_singleton.mp hj] at hzero
        exact (Finset.mem_union.mp hi).elim (fun h => hL0 i h hz) (fun h => hR0 i h hz)
      · have he := (Finset.mem_singleton.mp hj).trans (Finset.mem_singleton.mp hk).symm
        exact Finset.disjoint_left.mp hdis hLj (he ▸ hRk)
    · rintro ⟨_, hsub⟩
      rcases hT with ⟨i, hi, hz⟩ | ⟨⟨i, hi, hLi⟩, j, hj, hRj⟩
      · exact hsub.elim (fun hs => hL0 i (hs hi) hz) (fun hs => hR0 i (hs hi) hz)
      · exact hsub.elim (fun hs => Finset.disjoint_left.mp hdis (hs hj) hRj)
          (fun hs => Finset.disjoint_left.mp hdis hLi (hs hi))
  have hvanish (T : Finset (Fin n)) (hTne : T ≠ ∅) (hkeep : keep T) (hbad : ¬ connected T) :
      cumulant ((T.sort (· ≤ ·)).map fs.get) = 0 := by
    have h0 (i : Fin n) (hi : i ∈ T) : i.val ≠ 0 :=
      fun he => hbad (Or.inl ⟨i, hi, he⟩)
    have hsub : T ⊆ L ∨ T ⊆ R := by
      by_cases hL : ∃ i ∈ T, i ∈ L
      · left
        intro i hi
        rcases zero_or_lr i with he | hl | hr
        · exact (h0 i hi he).elim
        · exact hl
        · exact (hbad (Or.inr ⟨hL, i, hi, hr⟩)).elim
      · right
        intro i hi
        rcases zero_or_lr i with he | hl | hr
        · exact (h0 i hi he).elim
        · exact (hL ⟨i, hi, hl⟩).elim
        · exact hr
    have hcard : 3 ≤ T.card := by
      have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hTne)
      have h1 : T.card ≠ 1 := by
        intro hc
        obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
        have hi := Finset.mem_singleton_self i
        have hLorR : i ∈ L ∪ R := hsub.elim
          (fun hl => Finset.mem_union_left _ (hl hi)) (fun hr => Finset.mem_union_right _ (hr hi))
        exact hkeep.1 ⟨i, hLorR, rfl⟩
      have h2 : T.card ≠ 2 := fun hc => hkeep.2 ⟨hc, hsub⟩
      omega
    let s := (T.sort (· ≤ ·)).map w
    have hre : (T.sort (· ≤ ·)).map fs.get = s.map rectangle := by
      unfold s
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      exact hrect i (h0 i ((Finset.mem_sort (· ≤ ·)).mp hi))
    have hwidths : ∀ a ∈ s, 0 ≤ a := by
      intro a ha
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      exact hw0 i
    have hs : s.sum ≤ 1 := by
      unfold s
      rw [sum_sort_map]
      rcases hsub with hl | hr
      · apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hl (fun i _ _ => hw0 i))
        rw [hsumL]
        exact hA.2
      · apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hr (fun i _ _ => hw0 i))
        rw [hsumR]
        exact hB.2
    rw [cumulant_eq_delta_of_length (show 3 ≤ ((T.sort (· ≤ ·)).map fs.get).length by simpa using hcard),
      hre, delta_rectangles_eq_zero_of_sum _ hwidths hs]
  change partitionSum fs keep = partitionSum fs connected
  unfold partitionSum
  symm
  refine Finset.sum_subset ?_ ?_
  · intro P hP
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
    exact fun T hT => hmixed T (hP T hT)
  · intro P hP hnot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP hnot
    push Not at hnot
    obtain ⟨T, hT, hb⟩ := hnot
    exact Finset.prod_eq_zero hT (hvanish T (P.ne_bot hT) (hP T hT) hb)

/-- Lemma 24. Here the left-row labels are positions 1 through `A.length`. -/
theorem connected_partitions (h : FourierProfile) (A B : List ℝ)
    (hh : IsProfile h) (_hcont : ContinuousAt h 0)
    (hA : WidthsAdmissible A) (hB : WidthsAdmissible B)
    (_hs : radius h + A.sum + B.sum ≤ 2) :
    modelExpectation (stat h * wick (A.map rectangle) * wick (B.map rectangle)) =
      partitionSum (h :: (A ++ B).map rectangle) (fun T =>
        (∃ i ∈ T, i.val = 0) ∨
          ((∃ i ∈ T, 0 < i.val ∧ i.val ≤ A.length) ∧
            (∃ i ∈ T, A.length < i.val))) :=
  connected_partitions_of_profile h A B hh hA hB

end Chowla

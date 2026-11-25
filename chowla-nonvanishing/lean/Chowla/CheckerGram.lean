import Chowla.CheckerLabelled
import Chowla.Model.Scaling
import Chowla.GridSound
import Chowla.RowBounds
import Mathlib.Data.List.FinRange

namespace Chowla.Checker

open Set
open scoped BigOperators

private theorem widthIndices_pair {ι : Type} [LinearOrder ι] (w : ι → ℝ) {i j : ι}
    (hij : i ≠ j) (hi : w i ≤ 1) :
    (widthsOn w {i, j}).foldl min 1 = min (w i) (w j) := by
  have hp : (({i, j} : Finset ι).sort (· ≤ ·)).Perm [i, j] :=
    List.perm_of_nodup_nodup_toFinset_eq (({i, j} : Finset ι).sort_nodup _)
      (by simp [hij]) (by simp)
  unfold widthsOn
  rw [(hp.map w).foldl_eq' (fun x _ y _ a => by rw [min_right_comm])]
  simp [min_eq_right hi]

private theorem cast_pairWeight (a b : ℚ) :
    (pairWeight a b : ℝ) = 2 * (min (a : ℝ) (b : ℝ)) ^ 2 := by
  rw [pairWeight, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  by_cases h : a ≤ b
  · have he : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h
    rw [min_eq_left h, min_eq_left he]
  · have h' : b ≤ a := le_of_not_ge h
    have he : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast h'
    rw [min_eq_right h', min_eq_right he]

private theorem crossBlockWeight_pair {ι : Type} [LinearOrder ι]
    (L : Finset ι) (width : ι → ℚ) {i j : ι} (hi : i ∈ L) (hj : j ∉ L)
    (hwi : (width i : ℝ) ≤ 1) :
    crossBlockWeight L (fun a b => (pairWeight (width a) (width b) : ℝ)) {i, j} =
      2 * ((widthsOn (fun i => (width i : ℝ)) {i, j}).foldl min 1) ^ 2 := by
  classical
  have hne : i ≠ j := fun h => hj (h ▸ hi)
  simp [crossBlockWeight, Finset.card_pair hne, Finset.filter_insert, Finset.filter_singleton,
    hi, hj, cast_pairWeight, widthIndices_pair (fun a => (width a : ℝ)) hne hwi]

private theorem supportWeighted_paper (p : Spline) (A B : List ℝ) (hp : IsProfile p.toReal)
    (width : Fin (A ++ B).length → ℚ)
    (he : ∀ i, (A ++ B).get i = (width i : ℝ))
    (hwidth : ∀ i, (width i : ℝ) ∈ Ioc 0 1) :
    let L : Finset (Fin (A ++ B).length) := Finset.univ.filter (fun i => i.val < A.length)
    supportWeighted (crossBlockWeight L (fun i j => (pairWeight (width i) (width j) : ℝ)))
        (fun U => (contractionTerm (splinePrimitives p) (sortedWidths width U) : ℝ)) Finset.univ =
      crossMatchingSum p.toReal A B := by
  classical
  let Z := A ++ B
  let w : Fin Z.length → ℝ := Z.get
  let L : Finset (Fin Z.length) := Finset.univ.filter fun i => i.val < A.length
  let U : Finset (Fin Z.length) := Finset.univ
  let f := fun S => (contractionTerm (splinePrimitives p) (sortedWidths width S) : ℝ)
  let g := crossBlockWeight L (fun i j => (pairWeight (width i) (width j) : ℝ))
  have hw : w = fun i => (width i : ℝ) := funext he
  change supportWeighted g f U = _
  unfold supportWeighted crossMatchingSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P _
  let good := fun C : Finset (Fin Z.length) =>
    C.card = 1 ∨ (C.card = 2 ∧
      (∃ i ∈ C, i.val < A.length) ∧ (∃ i ∈ C, A.length ≤ i.val))
  have hgood_iff (C : Finset (Fin Z.length)) :
      good C ↔ C.card = 1 ∨
        (C.card = 2 ∧ (∃ i ∈ C, i ∈ L) ∧ (∃ i ∈ C, i ∉ L)) := by
    simp [good, L, not_lt]
  by_cases hP : ∀ C ∈ P.parts, good C
  · rw [if_pos hP]
    have hwgt (C : Finset (Fin Z.length)) (hC : C ∈ P.parts) :
        g C =
          if C.card = 2 then 2 * (widthsOn w C).foldl min 1 ^ 2 else 1 := by
      rcases (hgood_iff C).mp (hP C hC) with hn | ⟨hn, ⟨i, hi, hiL⟩, ⟨j, hj, hjL⟩⟩
      · simp [g, crossBlockWeight, hn]
      · have hne : i ≠ j := fun h => hjL (h ▸ hiL)
        have hCij : ({i, j} : Finset (Fin Z.length)) = C :=
          Finset.eq_of_subset_of_card_le (by simp [Finset.insert_subset_iff, hi, hj])
            (by rw [hn, Finset.card_pair hne])
        rw [if_pos hn, ← hCij]
        unfold g
        rw [crossBlockWeight_pair L width hiL hjL (hwidth i).2]
        rw [hw]
    rw [Finset.prod_congr rfl hwgt]
    congr 1
    have hS : U.filter (fun i => ∃ C ∈ P.parts, C = {i}) = U \ pairSupport P := by
      ext i
      simp only [Finset.mem_filter]
      have hh := singleton_mem_iff_notMem_pairSupport P
        (fun C hC => (hP C hC).imp id And.left) (i := i)
      constructor
      · rintro ⟨_, C, hC, rfl⟩
        exact hh.mp hC
      · intro h
        exact ⟨(Finset.mem_sdiff.mp h).1, {i}, hh.mpr h, rfl⟩
    rw [hS]
    unfold f
    rw [contractionTerm_finset p width _ hp (fun i _ => hwidth i)]
    simp only [widthsOn, show (A ++ B).get = fun i => (width i : ℝ) from funext he]
  · rw [if_neg hP]
    push Not at hP
    obtain ⟨C, hC, hbad⟩ := hP
    have hZero : g C = 0 := by
      rw [hgood_iff] at hbad
      have h1 : C.card ≠ 1 := fun h => hbad (Or.inl h)
      by_cases hc : C.card = 2
      · by_cases hL : ∃ i ∈ C, i ∈ L
        · have hR : C.filter (· ∉ L) = ∅ := Finset.filter_eq_empty_iff.mpr
            (fun i hi hin => hbad (Or.inr ⟨hc, hL, ⟨i, hi, hin⟩⟩))
          simp [g, crossBlockWeight, h1, hR]
        · have hf : C.filter (· ∈ L) = ∅ := Finset.filter_eq_empty_iff.mpr
            (fun i hi hin => hL ⟨i, hi, hin⟩)
          simp [g, crossBlockWeight, h1, hf]
      · simp [g, crossBlockWeight, h1, hc]
    rw [Finset.prod_eq_zero hC hZero, zero_mul]

private theorem cast_weighted (weights : List MatchingWeight) (f : List ℚ → ℚ) :
    (weightedSum weights f : ℝ) = realWeighted weights (fun xs => (f xs : ℝ)) := by
  induction weights with
  | nil => simp [weightedSum, realWeighted]
  | cons a as ih =>
    rw [weightedSum_cons, Rat.cast_add, Rat.cast_mul, ih]
    rfl

/-- The compressed rational contraction evaluates the mathematical finite partition sum. -/
theorem contraction_sound (p : Spline) (hp : IsProfile p.toReal) (A B : List ℚ)
    (hA : ∀ a ∈ A, (a : ℝ) ∈ Ioc 0 1) (hB : ∀ b ∈ B, (b : ℝ) ∈ Ioc 0 1) :
    (contraction (splinePrimitives p) A B : ℝ) =
      crossMatchingSum p.toReal (A.map fun a : ℚ => (a : ℝ)) (B.map fun b : ℚ => (b : ℝ)) := by
  classical
  let X := A.map fun a : ℚ => (a : ℝ)
  let Y := B.map fun a : ℚ => (a : ℝ)
  let Z := X ++ Y
  let T := A ++ B
  have hlen : Z.length = A.length + B.length := by simp [Z, X, Y]
  have hlenT : Z.length = T.length := by simpa [T] using hlen
  let w : Fin Z.length → ℚ := fun i => T.get (Fin.cast hlenT i)
  let L : Finset (Fin Z.length) := Finset.univ.filter fun i => i.val < X.length
  let eL : Fin A.length ↪ Fin Z.length :=
    ⟨fun i => ⟨i.val, by omega⟩, fun i j h => Fin.ext (congrArg (fun k : Fin Z.length => k.val) h)⟩
  let eR : Fin B.length ↪ Fin Z.length :=
    ⟨fun i => ⟨A.length + i.val, by omega⟩,
      fun i j h => Fin.ext (Nat.add_left_cancel (congrArg (fun k : Fin Z.length => k.val) h))⟩
  let l := (List.finRange A.length).map eL
  let r := (List.finRange B.length).map eR
  have hl : l.Nodup := (List.nodup_finRange _).map eL.injective
  have hr : r.Nodup := (List.nodup_finRange _).map eR.injective
  have hL (i : Fin Z.length) (hi : i ∈ l) : i ∈ L := by
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    simp [L, eL, X]
  have hR : Disjoint r.toFinset L := by
    refine Finset.disjoint_left.mpr ?_
    intro i hi hiL
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
    simp [L, eR, X] at hiL
  have hfull : (l ++ r).toFinset = Finset.univ := by
    ext i
    simp only [Finset.mem_univ, iff_true, List.mem_toFinset, List.mem_append]
    by_cases h : i.val < A.length
    · exact Or.inl (List.mem_map.mpr ⟨⟨i.val, h⟩, List.mem_finRange _, Fin.ext rfl⟩)
    · have hi : i.val < A.length + B.length := hlen ▸ i.isLt
      exact Or.inr (List.mem_map.mpr ⟨⟨i.val - A.length, by omega⟩,
        List.mem_finRange _, Fin.ext (by change A.length + (i.val - A.length) = i.val; omega)⟩)
  have hleft : l.map w = A := by
    simp only [l, List.map_map]
    refine Eq.trans ?_ (List.map_get_finRange A)
    apply List.map_congr_left
    intro i _
    exact List.getElem_append_left i.isLt
  have hright : r.map w = B := by
    simp only [r, List.map_map]
    refine Eq.trans ?_ (List.map_get_finRange B)
    apply List.map_congr_left
    intro i _
    change (A ++ B)[A.length + i.val] = B[i.val]
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    simp
  have he (i : Fin Z.length) : Z.get i = (w i : ℝ) := by
    by_cases hi : i.val < A.length
    · have hX : i.val < X.length := by simpa [X] using hi
      simp only [Z, w, T, List.get_eq_getElem, Fin.val_cast, List.getElem_append_left hX,
        List.getElem_append_left hi, X, List.getElem_map]
    · have hX : X.length ≤ i.val := by simpa [X] using Nat.le_of_not_gt hi
      simp only [Z, w, T, List.get_eq_getElem, Fin.val_cast, List.getElem_append_right hX,
        List.getElem_append_right (Nat.le_of_not_gt hi), X, Y, List.length_map, List.getElem_map]
  have hw (i : Fin Z.length) : (w i : ℝ) ∈ Ioc 0 1 := by
    rcases List.mem_append.mp (List.get_mem T (Fin.cast hlenT i)) with h | h
    · exact hA _ h
    · exact hB _ h
  rw [contraction_labelled, cast_weighted, ← hleft, ← hright]
  rw [labelledMatchingWeights_partition_sort w L l r hl hr hL hR, hfull, hleft, hright]
  exact supportWeighted_paper p X Y hp w he hw


/-- The exact rational Gram entry equals the model row inner product. -/
theorem gram_sound (r s : Rows.RowData) (hr : r.validWidths = true) (hs : s.validWidths = true) :
    (gram (prepare r) (prepare s) : ℝ) = innerRow r.toRow s.toRow := by
  obtain ⟨hra, hrs⟩ := r.validWidths_sound hr
  obtain ⟨hsa, hss⟩ := s.validWidths_sound hs
  have hrAdm := r.toRow_admissible_of_widths hra hrs
  have hsAdm := s.toRow_admissible_of_widths hsa hss
  have hrPos : 0 < 1 - r.widths.sum := by
    simp only [Rows.RowData.validWidths, Bool.and_eq_true, decide_eq_true_eq] at hr
    exact sub_pos.mpr hr.2
  have hsPos : 0 < 1 - s.widths.sum := by
    simp only [Rows.RowData.validWidths, Bool.and_eq_true, decide_eq_true_eq] at hs
    exact sub_pos.mpr hs.2
  have hrProfile : IsProfile (unweightedProfile r) := legendreProfile_isProfile _ _
  have hsProfile : IsProfile (unweightedProfile s) := legendreProfile_isProfile _ _
  let p := (prepare r).profile.convolution (prepare s).profile
  have hpEq := prepared_convolution_sound r s hrPos hsPos
  have hp : IsProfile p.toReal := by
    change IsProfile (((prepare r).profile.convolution (prepare s).profile).toReal)
    rw [hpEq]
    exact convolve_isProfile hrProfile hsProfile
  have hwidths (q : Rows.RowData) (h : ∀ t ∈ q.toRow.widths, t ∈ Ioo 0 1)
      (a : ℚ) (ha : a ∈ q.widths) : (a : ℝ) ∈ Ioc 0 1 :=
    let hh := h _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
    ⟨hh.1, hh.2.le⟩
  change ((r.weight * s.weight * contraction (splinePrimitives p) r.widths s.widths : ℚ) : ℝ) = _
  rw [Rat.cast_mul, Rat.cast_mul, contraction_sound p hp _ _ (hwidths r hra) (hwidths s hsa)]
  change _ * _ * crossMatchingSum
    (((prepare r).profile.convolution (prepare s).profile).toReal) r.toRow.widths s.toRow.widths = _
  rw [hpEq, innerRow_eq_crossMatchingSum r.toRow s.toRow hrAdm hsAdm,
    rowProfile_eq, rowProfile_eq,
    convolve_const_mul_head, convolve_const_mul_right, crossMatchingSum_const_mul,
    crossMatchingSum_const_mul, mul_assoc]

/-- The optimized Gram evaluator is sound for packed rows, including rows whose
weights have been updated after preparation. -/
theorem gramGrid_eq_innerRow_of_pack {l r : GridRow} (L R : Rows.RowData)
    (hl : l.PackedSound) (hr : r.PackedSound)
    (hlr : l.row = prepare L) (hrr : r.row = prepare R)
    (hL : L.validWidths = true) (hR : R.validWidths = true) :
    (gramGrid l r : ℝ) = innerRow L.toRow R.toRow := by
  rw [gramGrid_sound_of_pack hl hr, hlr, hrr, gram_sound L R hL hR]

theorem gramGrid_eq_innerRow (r s : Rows.RowData)
    (hr : r.validWidths = true) (hs : s.validWidths = true) :
    (gramGrid (prepareGrid r) (prepareGrid s) : ℝ) = innerRow r.toRow s.toRow := by
  rw [gramGrid_sound, gram_sound r s hr hs]

end Chowla.Checker

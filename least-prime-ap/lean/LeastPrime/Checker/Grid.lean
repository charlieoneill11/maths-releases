import LeastPrime.Checker.Compute
import LeastPrime.ProofDefs
import Mathlib.MeasureTheory.Measure.Real

/-! Set semantics and normalisation of the integer grid. -/

namespace LeastPrime.Checker

open MeasureTheory Set

noncomputable section

def grid (n : Nat) : ℝ := (n : ℝ) / (unit : ℝ)

theorem unit_pos : 0 < unit := by decide

theorem unit_real_pos : (0 : ℝ) < (unit : ℝ) := by exact_mod_cast unit_pos

@[simp] theorem grid_zero : grid 0 = 0 := by simp [grid]

@[simp] theorem grid_unit : grid unit = 1 := by simp [grid, unit_real_pos.ne']

theorem grid_le_iff {a b : Nat} : grid a ≤ grid b ↔ a ≤ b := by
  rw [grid, grid, div_le_div_iff_of_pos_right unit_real_pos]
  exact Nat.cast_le

theorem grid_lt_iff {a b : Nat} : grid a < grid b ↔ a < b := by
  rw [grid, grid, div_lt_div_iff_of_pos_right unit_real_pos]
  exact Nat.cast_lt

theorem grid_nonneg (n : Nat) : 0 ≤ grid n := by
  rw [← grid_zero, grid_le_iff]
  exact Nat.zero_le n

theorem grid_sub {a b : Nat} (h : b ≤ a) : grid (a - b) = grid a - grid b := by
  simp only [grid, Nat.cast_sub h]
  rw [sub_div]

def interval (I : GridInterval) : Set ℝ := Icc (grid I.1) (grid I.2)

def denote : GridSet → Set ℝ
  | [] => ∅
  | I :: rest => interval I ∪ denote rest

theorem mem_denote {T : GridSet} {x : ℝ} :
    x ∈ denote T ↔ ∃ I ∈ T, x ∈ interval I := by
  induction T with
  | nil => simp [denote]
  | cons I rest ih =>
    simp only [denote, mem_union, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨J, hJ, hx⟩)
      · exact ⟨I, Or.inl rfl, h⟩
      · exact ⟨J, Or.inr hJ, hx⟩
    · rintro ⟨J, rfl | hJ, hx⟩
      · exact Or.inl hx
      · exact Or.inr ⟨J, hJ, hx⟩

theorem denote_eq_intervalUnion (T : GridSet) :
    denote T = intervalUnion (T.map fun I => (grid I.1, grid I.2)) := by
  ext x
  simp only [mem_denote, intervalUnion, mem_iUnion, List.mem_map]
  constructor
  · rintro ⟨I, hI, hx⟩
    exact ⟨_, ⟨I, hI, rfl⟩, hx⟩
  · rintro ⟨_, ⟨I, hI, rfl⟩, hx⟩
    exact ⟨I, hI, hx⟩

def Good (I : GridInterval) : Prop := I.1 ≤ I.2 ∧ I.2 ≤ unit

def Segregated (T : GridSet) : Prop := T.Pairwise fun I J => I.2 < J.1

def Valid (T : GridSet) : Prop :=
  (∀ I ∈ T, Good I) ∧ Segregated T ∧ IsSymmetric (denote T)

theorem denote_subset_unit {T : GridSet} (hT : ∀ I ∈ T, Good I) : denote T ⊆ Icc 0 1 := by
  intro x hx
  obtain ⟨I, hi, hl, hu⟩ := mem_denote.mp hx
  exact ⟨(grid_nonneg _).trans hl, hu.trans (by rw [← grid_unit, grid_le_iff]; exact (hT I hi).2)⟩

theorem isClosedTarget_denote {T : GridSet} (hT : ∀ I ∈ T, Good I) : IsClosedTarget (denote T) := by
  refine ⟨_, ?_, denote_eq_intervalUnion T⟩
  intro I hI
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hI
  refine ⟨grid_nonneg _, grid_le_iff.mpr (hT J hJ).1, ?_⟩
  rw [← grid_unit, grid_le_iff]
  exact (hT J hJ).2

theorem interval_reflect {I : GridInterval} (hI : Good I) :
    interval (reflectInterval I) = reflect (interval I) := by
  have hl : I.1 ≤ unit := hI.1.trans hI.2
  ext x
  change x ∈ Icc (grid (unit - I.2)) (grid (unit - I.1)) ↔
    x ∈ (fun t : ℝ => 1 - t) '' Icc (grid I.1) (grid I.2)
  rw [grid_sub hI.2, grid_sub hl, grid_unit]
  constructor
  · intro hx
    exact ⟨1 - x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, by ring⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨by linarith [hy.2], by linarith [hy.1]⟩

theorem good_reflect {I : GridInterval} (hI : Good I) : Good (reflectInterval I) :=
  ⟨Nat.sub_le_sub_left hI.1 _, Nat.sub_le _ _⟩

theorem reflectInterval_reflectInterval {I : GridInterval} (hI : Good I) :
    reflectInterval (reflectInterval I) = I := by
  rcases I with ⟨a, b⟩
  rcases hI with ⟨hab, hb⟩
  simp only [reflectInterval, Prod.mk.injEq]
  exact ⟨by omega, by omega⟩

private theorem interval_merge {I J : GridInterval} (hIJ : I.1 ≤ J.1) (hJI : J.1 ≤ I.2) :
    interval (I.1, max I.2 J.2) = interval I ∪ interval J := by
  have hIJ' := grid_le_iff.mpr hIJ
  have hJI' := grid_le_iff.mpr hJI
  by_cases hmax : I.2 ≤ J.2
  · rw [max_eq_right hmax]
    ext x
    change x ∈ Icc (grid I.1) (grid J.2) ↔ x ∈ interval I ∪ interval J
    constructor
    · intro hx
      by_cases h : x ≤ grid I.2
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨hJI'.trans (le_of_not_ge h), hx.2⟩
    · rintro (hx | hx)
      · exact ⟨hx.1, hx.2.trans (grid_le_iff.mpr hmax)⟩
      · exact ⟨hIJ'.trans hx.1, hx.2⟩
  · rw [max_eq_left (le_of_not_ge hmax)]
    change interval I = interval I ∪ interval J
    refine (union_eq_left.mpr ?_).symm
    exact Icc_subset_Icc hIJ' (grid_le_iff.mpr (le_of_not_ge hmax))

private theorem mergeSorted_spec {current : GridInterval} {rest : GridSet}
    (hGood : ∀ I ∈ current :: rest, Good I)
    (hSort : (current :: rest).Pairwise (fun I J : GridInterval => I.1 ≤ J.1)) :
    Segregated (mergeSorted current rest) ∧
      (∀ I ∈ mergeSorted current rest, Good I ∧ current.1 ≤ I.1) ∧
      denote (mergeSorted current rest) = denote (current :: rest) := by
  induction rest generalizing current with
  | nil =>
    have hc := hGood current List.mem_cons_self
    simp [mergeSorted, Segregated, hc]
  | cons next rest ih =>
    simp only [mergeSorted]
    have hc := hGood current List.mem_cons_self
    have hn := hGood next (by simp)
    rw [List.pairwise_cons] at hSort
    by_cases hover : next.1 ≤ current.2
    · rw [if_pos hover]
      let J : GridInterval := (current.1, max current.2 next.2)
      have hJ : Good J := ⟨hc.1.trans (le_max_left _ _), max_le hc.2 hn.2⟩
      have hgood' : ∀ I ∈ J :: rest, Good I := by
        intro I h
        rcases List.mem_cons.mp h with rfl | h
        · exact hJ
        · exact hGood I (List.mem_cons_of_mem current (List.mem_cons_of_mem next h))
      have hsort' : List.Pairwise (fun I J : GridInterval => I.1 ≤ J.1) (J :: rest) := by
        rw [List.pairwise_cons]
        exact ⟨fun x hx => hSort.1 x (List.mem_cons_of_mem next hx), hSort.2.tail⟩
      obtain ⟨hseg, hall, hdenote⟩ := ih hgood' hsort'
      refine ⟨hseg, hall, ?_⟩
      rw [hdenote]
      simp only [denote, J]
      rw [interval_merge (hSort.1 next List.mem_cons_self) hover, union_assoc]
    · rw [if_neg hover]
      have hgood' : ∀ I ∈ next :: rest, Good I := fun I hi =>
        hGood I (List.mem_cons_of_mem current hi)
      obtain ⟨hseg, hall, hdenote⟩ := ih hgood' hSort.2
      have hsep : current.2 < next.1 := lt_of_not_ge hover
      refine ⟨List.pairwise_cons.mpr ⟨fun I hi => hsep.trans_le (hall I hi).2, hseg⟩, ?_, ?_⟩
      · intro I hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact ⟨hc, le_rfl⟩
        · exact ⟨(hall I hi).1, (hSort.1 next List.mem_cons_self).trans (hall I hi).2⟩
      · simp only [denote]
        rw [hdenote]
        rfl

theorem mergeIntervals_spec {T : GridSet} (hGood : ∀ I ∈ T, Good I) :
    Segregated (mergeIntervals T) ∧ (∀ I ∈ mergeIntervals T, Good I) ∧
      denote (mergeIntervals T) = denote T := by
  have hsort : (T.mergeSort intervalLE).Pairwise (fun I J : GridInterval => I.1 ≤ J.1) := by
    apply List.Pairwise.imp (R := fun a b => intervalLE a b = true)
    · intro I J h
      simp only [intervalLE, decide_eq_true_eq] at h
      rcases h with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    · apply List.pairwise_mergeSort
      · intro a b c ab bc
        simp only [intervalLE, decide_eq_true_eq] at *
        omega
      · intro a b
        simp only [Bool.or_eq_true, intervalLE, decide_eq_true_eq]
        omega
  have hperm : List.Perm (T.mergeSort intervalLE) T := List.mergeSort_perm _ _
  have hbefore : denote (T.mergeSort intervalLE) = denote T := by
    ext x
    simp only [mem_denote, hperm.mem_iff]
  have hGood' : ∀ I ∈ T.mergeSort intervalLE, Good I := fun I h =>
    hGood I (hperm.mem_iff.mp h)
  unfold mergeIntervals
  cases ht : T.mergeSort intervalLE with
  | nil =>
    rw [ht] at hbefore
    exact ⟨.nil, by simp, hbefore⟩
  | cons I tail =>
    rw [ht] at hGood' hsort hbefore
    obtain ⟨hseg, hall, hdenote⟩ := mergeSorted_spec hGood' hsort
    exact ⟨hseg, fun J hj => (hall J hj).1, hdenote.trans hbefore⟩

theorem grid_add (a b : Nat) : grid (a + b) = grid a + grid b := by
  simp [grid, add_div]

theorem measurableSet_interval (I : GridInterval) : MeasurableSet (interval I) :=
  measurableSet_Icc

theorem measurableSet_denote (T : GridSet) : MeasurableSet (denote T) := by
  induction T with
  | nil => exact MeasurableSet.empty
  | cons I T ih => exact (measurableSet_interval I).union ih

theorem volume_interval_ne_top (I : GridInterval) : volume (interval I) ≠ ⊤ :=
  measure_Icc_lt_top.ne

theorem volume_denote_ne_top (T : GridSet) : volume (denote T) ≠ ⊤ := by
  induction T with
  | nil => simp [denote]
  | cons I T ih => exact (measure_union_lt_top (volume_interval_ne_top I).lt_top ih.lt_top).ne

theorem disjoint_interval_of_high_lt_low {I J : GridInterval} (h : I.2 < J.1) :
    Disjoint (interval I) (interval J) := by
  refine Set.disjoint_left.mpr fun x hi hj => ?_
  exact (not_le_of_gt (grid_lt_iff.mpr h)) (hj.1.trans hi.2)

theorem disjoint_interval_denote {I : GridInterval} {T : GridSet}
    (h : ∀ J ∈ T, Disjoint (interval I) (interval J)) :
    Disjoint (interval I) (denote T) := by
  refine Set.disjoint_left.mpr fun _ hi hx => ?_
  obtain ⟨J, hj, hx⟩ := mem_denote.mp hx
  exact Set.disjoint_left.mp (h J hj) hi hx

theorem disjointIntervals_of_segregated {T : GridSet} (h : Segregated T) :
    T.Pairwise (fun I J => Disjoint (interval I) (interval J)) :=
  h.imp fun hIJ => disjoint_interval_of_high_lt_low hIJ

theorem disjointIntervals_of_descending {T : GridSet}
    (h : T.Pairwise fun I J => J.2 < I.1) :
    T.Pairwise (fun I J => Disjoint (interval I) (interval J)) :=
  h.imp fun hJI => (disjoint_interval_of_high_lt_low hJI).symm

theorem volume_interval (I : GridInterval) (h : I.1 ≤ I.2) :
    volume.real (interval I) = grid (width I) := by
  rw [interval, Real.volume_real_Icc_of_le (grid_le_iff.mpr h), width, grid_sub h]

theorem volume_denote {T : GridSet} (hGood : ∀ I ∈ T, Good I)
    (hDisj : T.Pairwise (fun I J => Disjoint (interval I) (interval J))) :
    volume.real (denote T) = grid (targetLength T) := by
  induction T with
  | nil => simp [denote, targetLength]
  | cons I T ih =>
    rw [List.pairwise_cons] at hDisj
    rw [denote, measureReal_union (disjoint_interval_denote hDisj.1) (measurableSet_denote T)
      (volume_interval_ne_top I) (volume_denote_ne_top T),
      volume_interval I (hGood I List.mem_cons_self).1,
      ih (fun J hj => hGood J (List.mem_cons_of_mem I hj)) hDisj.2]
    simp only [targetLength, List.map_cons, List.sum_cons, grid_add]


end

end LeastPrime.Checker

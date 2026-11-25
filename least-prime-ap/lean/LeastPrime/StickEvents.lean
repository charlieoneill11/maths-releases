import LeastPrime.ProofDefs
import Mathlib.MeasureTheory.Measure.Real

/-! The two stick-breaking events and their elementary subset-sum properties. -/

namespace LeastPrime

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

def subsetSum {j : ℕ} (S : Finset (Fin j)) (v : Fin j → ℝ) : ℝ := ∑ i ∈ S, v i

private theorem subsetSum_compl {j : ℕ} (S : Finset (Fin j)) (v : Fin j → ℝ) :
    subsetSum Sᶜ v + subsetSum S v = ∑ i, v i :=
  Finset.sum_compl_add_sum S v

theorem continuous_subsetSum {j : ℕ} (S : Finset (Fin j)) :
    Continuous (subsetSum S) := by
  unfold subsetSum
  fun_prop

theorem continuous_remainder (j : ℕ) : Continuous (@remainder j) := by
  unfold remainder
  fun_prop

theorem remainder_nonneg {j : ℕ} {v : Fin j → ℝ} (hv : v ∈ simplex j) :
    0 ≤ remainder v := sub_nonneg.mpr hv.2

theorem isClosed_simplex (j : ℕ) : IsClosed (simplex j) := by
  have h : simplex j = (⋂ i : Fin j, (fun v : Fin j → ℝ => v i) ⁻¹' Icc 0 1) ∩
      {v : Fin j → ℝ | ∑ i, v i ≤ 1} := by
    ext v
    simp [simplex]
  rw [h]
  exact (isClosed_iInter fun i => isClosed_Icc.preimage (continuous_apply i)).inter
    (isClosed_le (by fun_prop) continuous_const)

/-- The endpoint-only choice uses the initial empty or full remainder. The interval choice
allows every intermediate amount. -/
def remainderAllowed (wholeOnly : Bool) (r y : ℝ) : Prop :=
  if wholeOnly then y = 0 ∨ y = r else y ∈ Icc 0 r

/-- Common representation of the two events, using a single remainder length. -/
def stickEvent (wholeOnly : Bool) (j : ℕ) (T : Set ℝ) : Set (Fin j → ℝ) :=
  {v | v ∈ simplex j ∧ ∃ S : Finset (Fin j), ∃ y : ℝ,
      remainderAllowed wholeOnly (remainder v) y ∧ subsetSum S v + y ∈ T}

def probability (wholeOnly : Bool) (j : ℕ) (T : Set ℝ) : ℝ :=
  (stickLaw j).real (stickEvent wholeOnly j T)

theorem stickEvent_true (j : ℕ) (T : Set ℝ) : stickEvent true j T = E j T := by
  ext v
  constructor
  · rintro ⟨hv, S, y, hy, hT⟩
    rcases (show y = 0 ∨ y = remainder v from hy) with rfl | rfl
    · exact ⟨hv, S, 0, Or.inl rfl, by simpa [subsetSum] using hT⟩
    · exact ⟨hv, S, 1, Or.inr rfl, by simpa [subsetSum] using hT⟩
  · rintro ⟨hv, S, ε, hε, hT⟩
    rcases hε with rfl | rfl
    · exact ⟨hv, S, 0, Or.inl rfl, by simpa [subsetSum] using hT⟩
    · exact ⟨hv, S, remainder v, Or.inr rfl, by simpa [subsetSum] using hT⟩

theorem stickEvent_false (j : ℕ) (T : Set ℝ) : stickEvent false j T = F j T := rfl

theorem probability_true (j : ℕ) (T : Set ℝ) : probability true j T = p j T := by
  rw [probability, stickEvent_true, p]

theorem probability_false (j : ℕ) (T : Set ℝ) : probability false j T = q j T := rfl

theorem remainderAllowed_zero (wholeOnly : Bool) {r : ℝ} (hr : 0 ≤ r) :
    remainderAllowed wholeOnly r 0 := by
  cases wholeOnly <;> simp [remainderAllowed, hr]

theorem remainderAllowed_nonneg {wholeOnly : Bool} {r y : ℝ} (hr : 0 ≤ r)
    (hy : remainderAllowed wholeOnly r y) : 0 ≤ y := by
  cases wholeOnly
  · exact hy.1
  · rcases (show y = 0 ∨ y = r from hy) with rfl | rfl
    · exact le_rfl
    · exact hr

theorem remainderAllowed_le {wholeOnly : Bool} {r y : ℝ} (hr : 0 ≤ r)
    (hy : remainderAllowed wholeOnly r y) : y ≤ r := by
  cases wholeOnly
  · exact hy.2
  · rcases (show y = 0 ∨ y = r from hy) with rfl | rfl
    · exact hr
    · exact le_rfl

theorem remainderAllowed_sub {wholeOnly : Bool} {r y : ℝ}
    (hy : remainderAllowed wholeOnly r y) : remainderAllowed wholeOnly r (r - y) := by
  cases wholeOnly
  · exact ⟨sub_nonneg.mpr hy.2, sub_le_self _ hy.1⟩
  · rcases (show y = 0 ∨ y = r from hy) with rfl | rfl
    · exact Or.inr (sub_zero _)
    · exact Or.inl (sub_self _)

theorem remainderAllowed_mul {wholeOnly : Bool} {a r y : ℝ} (ha : 0 < a) :
    remainderAllowed wholeOnly (a * r) (a * y) ↔ remainderAllowed wholeOnly r y := by
  cases wholeOnly <;> simp [remainderAllowed, ha, ha.ne', mul_nonneg_iff_of_pos_left]

theorem complement_witness {wholeOnly : Bool} {j : ℕ} {v : Fin j → ℝ}
    {S : Finset (Fin j)} {y : ℝ} (hy : remainderAllowed wholeOnly (remainder v) y) :
    remainderAllowed wholeOnly (remainder v) (remainder v - y) ∧
      subsetSum Sᶜ v + (remainder v - y) = 1 - (subsetSum S v + y) := by
  refine ⟨remainderAllowed_sub hy, ?_⟩
  have := subsetSum_compl S v
  unfold remainder
  linarith

theorem reflect_reflect (T : Set ℝ) : reflect (reflect T) = T := by
  ext t
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    simpa using hw
  · intro ht
    exact ⟨1 - t, ⟨t, ht, rfl⟩, by ring⟩

theorem symmetric_sub {T : Set ℝ} (hs : IsSymmetric T) {t : ℝ} (ht : t ∈ T) : 1 - t ∈ T :=
  hs.symm ▸ ⟨t, ht, rfl⟩

theorem stickEvent_mono {wholeOnly : Bool} {j : ℕ} {S T : Set ℝ} (hst : S ⊆ T) :
    stickEvent wholeOnly j S ⊆ stickEvent wholeOnly j T := by
  rintro v ⟨hv, A, y, hy, h⟩
  exact ⟨hv, A, y, hy, hst h⟩

theorem probability_mono {wholeOnly : Bool} {j : ℕ} {S T : Set ℝ} (hst : S ⊆ T) :
    probability wholeOnly j S ≤ probability wholeOnly j T :=
  measureReal_mono (stickEvent_mono hst)

theorem probability_nonneg (wholeOnly : Bool) (j : ℕ) (T : Set ℝ) :
    0 ≤ probability wholeOnly j T := measureReal_nonneg

theorem probability_le_one (wholeOnly : Bool) (j : ℕ) (T : Set ℝ) :
    probability wholeOnly j T ≤ 1 := by
  rw [← probReal_univ (μ := stickLaw j)]
  exact measureReal_mono (subset_univ _)

theorem p_nonneg (j : ℕ) (T : Set ℝ) : 0 ≤ p j T := measureReal_nonneg

theorem q_nonneg (j : ℕ) (T : Set ℝ) : 0 ≤ q j T := measureReal_nonneg

theorem p_le_one (j : ℕ) (T : Set ℝ) : p j T ≤ 1 := by
  simpa only [probability_true] using probability_le_one true j T

theorem q_le_one (j : ℕ) (T : Set ℝ) : q j T ≤ 1 :=
  probability_le_one false j T

theorem p_mono {j : ℕ} {S T : Set ℝ} (hst : S ⊆ T) : p j S ≤ p j T := by
  simpa only [probability_true] using probability_mono (wholeOnly := true) (j := j) hst

theorem q_mono {j : ℕ} {S T : Set ℝ} (hst : S ⊆ T) : q j S ≤ q j T := by
  simpa only [probability_false] using probability_mono (wholeOnly := false) (j := j) hst

theorem stickEvent_union (wholeOnly : Bool) (j : ℕ) (S T : Set ℝ) :
    stickEvent wholeOnly j (S ∪ T) = stickEvent wholeOnly j S ∪ stickEvent wholeOnly j T := by
  ext v
  constructor
  · rintro ⟨hv, A, y, hy, hS | hT⟩
    · exact Or.inl ⟨hv, A, y, hy, hS⟩
    · exact Or.inr ⟨hv, A, y, hy, hT⟩
  · rintro (⟨hv, A, y, hy, hS⟩ | ⟨hv, A, y, hy, hT⟩)
    · exact ⟨hv, A, y, hy, Or.inl hS⟩
    · exact ⟨hv, A, y, hy, Or.inr hT⟩

theorem stickEvent_reflect (wholeOnly : Bool) (j : ℕ) (T : Set ℝ) :
    stickEvent wholeOnly j (reflect T) = stickEvent wholeOnly j T := by
  suffices h : ∀ U : Set ℝ, stickEvent wholeOnly j U ⊆ stickEvent wholeOnly j (reflect U) by
    refine le_antisymm ?_ (h T)
    simpa only [reflect_reflect] using h (reflect T)
  rintro U v ⟨hv, A, y, hy, hU⟩
  obtain ⟨hy', heq⟩ := complement_witness (S := A) (v := v) hy
  exact ⟨hv, Aᶜ, remainder v - y, hy', ⟨subsetSum A v + y, hU, heq.symm⟩⟩

theorem stickEvent_complement (wholeOnly : Bool) (j : ℕ) (T : Set ℝ) :
    stickEvent wholeOnly j (T ∪ reflect T) = stickEvent wholeOnly j T := by
  rw [stickEvent_union, stickEvent_reflect, union_self]

theorem probability_complement (wholeOnly : Bool) (j : ℕ) (T : Set ℝ) :
    probability wholeOnly j T = probability wholeOnly j (T ∪ reflect T) := by
  rw [probability, probability, stickEvent_complement]

theorem p_complement (j : ℕ) (T : Set ℝ) : p j T = p j (T ∪ reflect T) := by
  simpa only [probability_true] using probability_complement true j T

theorem q_complement (j : ℕ) (T : Set ℝ) : q j T = q j (T ∪ reflect T) := by
  simpa only [probability_false] using probability_complement false j T

theorem mem_intervalUnion {intervals : List (ℝ × ℝ)} {x : ℝ} :
    x ∈ intervalUnion intervals ↔ ∃ I ∈ intervals, x ∈ Icc I.1 I.2 := by
  simp only [intervalUnion, mem_iUnion, exists_prop]

theorem isClosed_intervalUnion (intervals : List (ℝ × ℝ)) : IsClosed (intervalUnion intervals) := by
  classical
  apply Set.Finite.isClosed_biUnion
  · exact intervals.toFinset.finite_toSet.subset (by simpa using subset_rfl)
  · intro I hI
    exact isClosed_Icc

theorem closedTarget_isClosed {T : Set ℝ} (hT : IsClosedTarget T) : IsClosed T := by
  obtain ⟨intervals, _, rfl⟩ := hT
  exact isClosed_intervalUnion _

theorem closedTarget_subset {T : Set ℝ} (hT : IsClosedTarget T) : T ⊆ Icc 0 1 := by
  obtain ⟨intervals, hi, rfl⟩ := hT
  intro x hx
  obtain ⟨I, hI, hxI⟩ := mem_intervalUnion.mp hx
  exact ⟨(hi I hI).1.trans hxI.1, hxI.2.trans (hi I hI).2.2⟩

theorem eventTrue_eq (j : ℕ) (T : Set ℝ) :
    stickEvent true j T = simplex j ∩
      ⋃ S : Finset (Fin j), (subsetSum S ⁻¹' T) ∪ ((fun v => subsetSum S v + remainder v) ⁻¹' T) := by
  ext v
  constructor
  · rintro ⟨hv, S, y, hy, hT⟩
    rcases (show y = 0 ∨ y = remainder v from hy) with rfl | rfl
    · exact ⟨hv, mem_iUnion.mpr ⟨S, Or.inl (by simpa using hT)⟩⟩
    · exact ⟨hv, mem_iUnion.mpr ⟨S, Or.inr hT⟩⟩
  · rintro ⟨hv, hS⟩
    obtain ⟨S, h | h⟩ := mem_iUnion.mp hS
    · exact ⟨hv, S, 0, Or.inl rfl, by simpa using h⟩
    · exact ⟨hv, S, remainder v, Or.inr rfl, h⟩

theorem eventFalse_eq (j : ℕ) (intervals : List (ℝ × ℝ))
    (hi : ∀ I ∈ intervals, I.1 ≤ I.2) :
    stickEvent false j (intervalUnion intervals) = simplex j ∩
      ⋃ S : Finset (Fin j), ⋃ I ∈ intervals,
        {v | subsetSum S v ≤ I.2} ∩ {v | I.1 ≤ subsetSum S v + remainder v} := by
  ext v
  constructor
  · rintro ⟨hv, S, y, hy, hT⟩
    obtain ⟨I, hI, ht⟩ := mem_intervalUnion.mp hT
    have hy' : y ∈ Icc 0 (remainder v) := hy
    refine ⟨hv, mem_iUnion.mpr ⟨S, mem_iUnion.mpr ⟨I, mem_iUnion.mpr ⟨hI, ?_⟩⟩⟩⟩
    constructor
    · change subsetSum S v ≤ I.2
      linarith [hy'.1, ht.2]
    · change I.1 ≤ subsetSum S v + remainder v
      linarith [hy'.2, ht.1]
  · rintro ⟨hv, hs⟩
    obtain ⟨S, hS⟩ := mem_iUnion.mp hs
    obtain ⟨I, hI⟩ := mem_iUnion.mp hS
    obtain ⟨hmem, hle⟩ := mem_iUnion.mp hI
    have h₁ : subsetSum S v ≤ I.2 := hle.1
    have h₂ : I.1 ≤ subsetSum S v + remainder v := hle.2
    refine ⟨hv, S, max 0 (I.1 - subsetSum S v), ?_, mem_intervalUnion.mpr ⟨I, hmem, ?_⟩⟩
    · exact ⟨le_max_left _ _, max_le (remainder_nonneg hv) (by linarith)⟩
    · constructor
      · linarith [le_max_right 0 (I.1 - subsetSum S v)]
      · rw [add_max]
        exact max_le (by simpa using h₁) (by linarith [hi I hmem])

theorem isClosed_stickEvent (wholeOnly : Bool) (j : ℕ) {T : Set ℝ}
    (hT : IsClosedTarget T) : IsClosed (stickEvent wholeOnly j T) := by
  classical
  cases wholeOnly
  · obtain ⟨intervals, hi, rfl⟩ := hT
    rw [eventFalse_eq j intervals (fun I hI => (hi I hI).2.1)]
    apply (isClosed_simplex j).inter
    refine isClosed_iUnion_of_finite fun S => Set.Finite.isClosed_biUnion ?_ (fun I _ => ?_)
    · exact intervals.toFinset.finite_toSet.subset (by simpa using subset_rfl)
    · exact (isClosed_le (continuous_subsetSum S) continuous_const).inter
        (isClosed_le continuous_const ((continuous_subsetSum S).add (continuous_remainder j)))
  · rw [eventTrue_eq]
    exact (isClosed_simplex j).inter <| isClosed_iUnion_of_finite fun S =>
      ((closedTarget_isClosed hT).preimage (continuous_subsetSum S)).union
        ((closedTarget_isClosed hT).preimage ((continuous_subsetSum S).add (continuous_remainder j)))

theorem isClosed_E (j : ℕ) {T : Set ℝ} (hT : IsClosedTarget T) : IsClosed (E j T) := by
  rw [← stickEvent_true]
  exact isClosed_stickEvent true j hT

theorem isClosed_F (j : ℕ) {T : Set ℝ} (hT : IsClosedTarget T) : IsClosed (F j T) :=
  isClosed_stickEvent false j hT

theorem cell_bounds (j : ℕ) {T : Set ℝ} {a b r : ℝ} {leftIntervals : List (ℝ × ℝ)}
    (ha : 0 < a) (_hb : b ≤ 1) (hr : r ∈ Ioo a b)
    (hintervals : T ∩ Icc 0 r = intervalUnion leftIntervals)
    (hend : ∀ I ∈ leftIntervals, 0 ≤ I.1 ∧ I.1 ≤ I.2 ∧ I.2 ≤ a) :
    p j (cellInner a b leftIntervals) ≤ p j (residualTarget r T) ∧
      q j (residualTarget r T) ≤ q j (cellOuter a b leftIntervals) := by
  have hr₀ : 0 < r := ha.trans hr.1
  have hb₀ : 0 < b := hr₀.trans hr.2
  simp only [residualTarget, ← p_complement, ← q_complement]
  constructor
  · apply p_mono
    intro x hx
    obtain ⟨_, hL, hxI⟩ := mem_intervalUnion.mp hx
    obtain ⟨⟨l, u⟩, hI, rfl⟩ := List.mem_map.mp hL
    have hl : 0 ≤ l := (hend (l, u) hI).1
    have hu : 0 ≤ u := hl.trans (hend (l, u) hI).2.1
    have hxl : l / r ≤ x := (div_le_div_of_nonneg_left hl ha hr.1.le).trans hxI.1
    have hxu : x ≤ u / r := hxI.2.trans (div_le_div_of_nonneg_left hu hr₀ hr.2.le)
    refine ⟨x * r, ?_, (mul_div_cancel_right₀ x hr₀.ne')⟩
    rw [hintervals]
    exact mem_intervalUnion.mpr ⟨(l, u), hI, (div_le_iff₀ hr₀).mp hxl, (le_div_iff₀ hr₀).mp hxu⟩
  · apply q_mono
    rintro x ⟨y, hy, rfl⟩
    rw [hintervals] at hy
    obtain ⟨⟨l, u⟩, hI, hyI⟩ := mem_intervalUnion.mp hy
    have hl : 0 ≤ l := (hend (l, u) hI).1
    have hu : 0 ≤ u := hl.trans (hend (l, u) hI).2.1
    refine mem_intervalUnion.mpr ⟨(l / b, u / a), List.mem_map.mpr ⟨(l,u), hI, rfl⟩, ?_⟩
    exact ⟨(div_le_div_of_nonneg_left hl hr₀ hr.2.le).trans (div_le_div_of_nonneg_right hyI.1 hr₀.le),
      (div_le_div_of_nonneg_right hyI.2 hr₀.le).trans (div_le_div_of_nonneg_left hu ha hr.1.le)⟩

end

end LeastPrime

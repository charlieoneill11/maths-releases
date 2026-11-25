import LeastPrime.StickEvents
import Mathlib.Data.Finset.Preimage
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Disintegrating the two stick-breaking events along the first break. -/

namespace LeastPrime

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

def unitCube (j : ℕ) : Set (Fin j → ℝ) := univ.pi fun _ => Icc 0 1

theorem mem_unitCube {j : ℕ} {u : Fin j → ℝ} :
    u ∈ unitCube j ↔ ∀ i, u i ∈ Icc (0 : ℝ) 1 := by
  simp only [unitCube, Set.mem_pi, mem_univ, true_implies]

theorem measurableSet_unitCube (j : ℕ) : MeasurableSet (unitCube j) :=
  (MeasurableSet.pi countable_univ (fun _ _ => measurableSet_Icc)).congr (by rfl)

def cubeLaw (j : ℕ) : Measure (Fin j → ℝ) := volume.restrict (unitCube j)

instance instIsProbabilityMeasureCubeLaw (j : ℕ) : IsProbabilityMeasure (cubeLaw j) where
  measure_univ := by
    rw [cubeLaw, Measure.restrict_apply_univ, unitCube, volume_pi_pi]
    simp [Real.volume_Icc]

theorem stickLaw_eq_map (j : ℕ) : stickLaw j = (cubeLaw j).map (stick j) := rfl

theorem ae_mem_cubeLaw (j : ℕ) : ∀ᵐ u ∂(cubeLaw j), u ∈ unitCube j :=
  ae_restrict_mem (measurableSet_unitCube j)

theorem stick_succ_zero {j : ℕ} (u : Fin (j + 1) → ℝ) :
    stick (j + 1) u 0 = u 0 := by simp [stick]

theorem stick_succ_apply {j : ℕ} (u : Fin (j + 1) → ℝ) (i : Fin j) :
    stick (j + 1) u i.succ = (1 - u 0) * stick j (fun k => u k.succ) i := by
  simp only [stick, Finset.prod_filter, Fin.prod_univ_succ, if_pos (Fin.succ_pos i),
    Fin.succ_lt_succ_iff]
  ring

theorem remainder_stick_succ {j : ℕ} (u : Fin (j + 1) → ℝ) :
    remainder (stick (j + 1) u) = (1 - u 0) * remainder (stick j (fun i => u i.succ)) := by
  unfold remainder
  simp only [Fin.sum_univ_succ, stick_succ_zero, stick_succ_apply, ← Finset.mul_sum]
  ring

theorem stick_mem_simplex {j : ℕ} {u : Fin j → ℝ} (hu : u ∈ unitCube j) :
    stick j u ∈ simplex j := by
  induction j with
  | zero => exact ⟨fun i => Fin.elim0 i, by simp⟩
  | succ j ih =>
    have huu := mem_unitCube.mp hu
    have htail := ih (u := fun i => u i.succ) (mem_unitCube.mpr fun i => huu i.succ)
    have hr : 0 ≤ 1 - u 0 := sub_nonneg.mpr (huu 0).2
    refine ⟨?_, sub_nonneg.mp ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => simpa only [stick_succ_zero] using huu 0
      | succ i =>
        rw [stick_succ_apply]
        exact ⟨mul_nonneg hr (htail.1 i).1,
          (mul_le_of_le_one_right hr (htail.1 i).2).trans (sub_le_self _ (huu 0).1)⟩
    · change 0 ≤ remainder (stick (j + 1) u)
      rw [remainder_stick_succ]
      exact mul_nonneg hr (remainder_nonneg htail)

theorem stickLaw_simplex (j : ℕ) : ∀ᵐ v ∂(stickLaw j), v ∈ simplex j := by
  rw [stickLaw_eq_map]
  apply (ae_map_iff (p := fun v => v ∈ simplex j) (measurable_stick j).aemeasurable
    (isClosed_simplex j).measurableSet).mpr
  exact (ae_mem_cubeLaw j).mono fun u hu => stick_mem_simplex hu

theorem probability_one_of_zero_mem (wholeOnly : Bool) {j : ℕ} {T : Set ℝ} (hT : 0 ∈ T) :
    probability wholeOnly j T = 1 := by
  rw [probability, ← probReal_univ (μ := stickLaw j)]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [stickLaw_simplex j] with v hv
  apply propext
  exact ⟨fun _ => mem_univ v, fun _ =>
    ⟨hv, ∅, 0, remainderAllowed_zero _ (remainder_nonneg hv), by simpa [subsetSum] using hT⟩⟩

theorem probability_empty (wholeOnly : Bool) (j : ℕ) : probability wholeOnly j ∅ = 0 := by
  have h : stickEvent wholeOnly j ∅ = ∅ := by
    ext v
    constructor
    · rintro ⟨_, _, _, _, ht⟩
      exact ht
    · exact False.elim
  simp [probability, h]

theorem p_one_of_zero_mem {j : ℕ} {T : Set ℝ} (hT : 0 ∈ T) : p j T = 1 := by
  simpa only [probability_true] using probability_one_of_zero_mem true (j := j) hT

theorem q_one_of_zero_mem {j : ℕ} {T : Set ℝ} (hT : 0 ∈ T) : q j T = 1 :=
  probability_one_of_zero_mem false hT

theorem p_empty (j : ℕ) : p j ∅ = 0 := by
  simpa only [probability_true] using probability_empty true j

theorem q_empty (j : ℕ) : q j ∅ = 0 :=
  probability_empty false j

theorem probability_residual_one (wholeOnly : Bool) (j : ℕ) {T : Set ℝ} {r : ℝ}
    (hr : 0 < r) (hT : r ∈ T) : probability wholeOnly j (residualTarget r T) = 1 := by
  apply probability_one_of_zero_mem
  right
  have h₁ : (1 : ℝ) ∈ rescale r T := ⟨r, ⟨hT, hr.le, le_rfl⟩, div_self hr.ne'⟩
  exact ⟨1, h₁, sub_self 1⟩

theorem p_residual_one (j : ℕ) {T : Set ℝ} {r : ℝ} (hr : 0 < r) (hT : r ∈ T) :
    p j (residualTarget r T) = 1 := by
  simpa only [probability_true] using probability_residual_one true j hr hT

theorem q_residual_one (j : ℕ) {T : Set ℝ} {r : ℝ} (hr : 0 < r) (hT : r ∈ T) :
    q j (residualTarget r T) = 1 :=
  probability_residual_one false j hr hT

/-- Split a symmetric target witness so that it uses only the residual stick. -/
private theorem stickEvent_without_head {wholeOnly : Bool} {j : ℕ} {T : Set ℝ}
    (hs : IsSymmetric T) {v : Fin (j + 1) → ℝ}
    (hv : v ∈ stickEvent wholeOnly (j + 1) T) :
    ∃ S : Finset (Fin (j + 1)), 0 ∉ S ∧ ∃ y : ℝ,
      remainderAllowed wholeOnly (remainder v) y ∧ subsetSum S v + y ∈ T := by
  obtain ⟨_, S, y, hy, hT⟩ := hv
  by_cases h0 : (0 : Fin (j + 1)) ∈ S
  · obtain ⟨hy', heq⟩ := complement_witness (S := S) (v := v) hy
    exact ⟨Sᶜ, by simpa using h0, remainder v - y, hy', heq ▸ symmetric_sub hs hT⟩
  · exact ⟨S, h0, y, hy, hT⟩

private theorem map_tail_subset {j : ℕ} (S : Finset (Fin (j + 1))) (h0 : 0 ∉ S) :
    (S.preimage (Fin.succEmb j) (Fin.succEmb j).injective.injOn).map (Fin.succEmb j) = S := by
  ext i
  cases i using Fin.cases with
  | zero =>
    simp [Finset.mem_map, h0]
  | succ i =>
    change (Fin.succEmb j) i ∈ _ ↔ _
    simp [Finset.mem_preimage]

private theorem subsetSum_tail {j : ℕ} (u : Fin (j + 1) → ℝ) (S : Finset (Fin j)) :
    subsetSum (S.map (Fin.succEmb j)) (stick (j + 1) u) =
      (1 - u 0) * subsetSum S (stick j (fun i => u i.succ)) := by
  simp only [subsetSum, Finset.sum_map, Fin.coe_succEmb, stick_succ_apply, Finset.mul_sum]

theorem subsetSum_remainder_mem_unit {wholeOnly : Bool} {j : ℕ} {v : Fin j → ℝ}
    (hv : v ∈ simplex j) (S : Finset (Fin j)) {y : ℝ}
    (hy : remainderAllowed wholeOnly (remainder v) y) :
    subsetSum S v + y ∈ Icc (0 : ℝ) 1 := by
  have hsum : subsetSum S v ≤ ∑ i, v i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => (hv.1 i).1)
  have h₀ : 0 ≤ subsetSum S v := Finset.sum_nonneg fun i _ => (hv.1 i).1
  refine ⟨add_nonneg h₀ (remainderAllowed_nonneg (remainder_nonneg hv) hy), ?_⟩
  have hy' := remainderAllowed_le (remainder_nonneg hv) hy
  unfold remainder at hy'
  linarith

/-- The equivalent residual event for a fixed positive remainder of the first break. -/
theorem stickEvent_stick_succ_iff {wholeOnly : Bool} {j : ℕ} {T : Set ℝ}
    (hs : IsSymmetric T) {u : Fin (j + 1) → ℝ} (hu : u ∈ unitCube (j + 1))
    (hr : 0 < 1 - u 0) :
    stick (j + 1) u ∈ stickEvent wholeOnly (j + 1) T ↔
      stick j (fun i => u i.succ) ∈ stickEvent wholeOnly j (rescale (1 - u 0) T) := by
  let v := stick j (fun i => u i.succ)
  let r := 1 - u 0
  have htail : v ∈ simplex j := stick_mem_simplex (mem_unitCube.mpr fun i => (mem_unitCube.mp hu) i.succ)
  have hrem : remainder (stick (j + 1) u) = r * remainder v := remainder_stick_succ u
  constructor
  · intro h
    obtain ⟨S, h0, y, hy, hsum⟩ := stickEvent_without_head hs h
    let A := S.preimage (Fin.succEmb j) (Fin.succEmb j).injective.injOn
    have hA : A.map (Fin.succEmb j) = S := map_tail_subset S h0
    have hy' : remainderAllowed wholeOnly (remainder v) (y / r) := by
      rw [hrem] at hy
      apply (remainderAllowed_mul hr).mp
      rw [show r * (y / r) = y from mul_div_cancel₀ y hr.ne']
      exact hy
    have htotal : r * (subsetSum A v + y / r) = subsetSum S (stick (j + 1) u) + y := by
      rw [← hA, subsetSum_tail]
      change r * (subsetSum A v + y / r) = r * subsetSum A v + y
      rw [mul_add, mul_div_cancel₀ _ hr.ne']
    refine ⟨htail, A, y / r, hy', ⟨_, ⟨hsum, ?_⟩, ?_⟩⟩
    · rw [← htotal]
      have h := subsetSum_remainder_mem_unit htail A hy'
      exact ⟨mul_nonneg hr.le h.1, mul_le_of_le_one_right hr.le h.2⟩
    · change (subsetSum S (stick (j + 1) u) + y) / r = subsetSum A v + y / r
      rw [← htotal, mul_comm r, mul_div_cancel_right₀ _ hr.ne']
  · rintro ⟨_, S, y, hy, ht⟩
    obtain ⟨z, hz, heq⟩ := ht
    refine ⟨stick_mem_simplex hu, S.map (Fin.succEmb j), r * y, ?_, ?_⟩
    · rw [hrem]
      exact (remainderAllowed_mul hr).mpr hy
    · rw [subsetSum_tail]
      have hz' : z = r * (subsetSum S v + y) := by
        rw [← heq]
        exact (mul_div_cancel₀ z hr.ne').symm
      rw [hz', mul_add] at hz
      exact hz.1

theorem mem_rescale_iff {r x : ℝ} {T : Set ℝ} (hr : 0 < r) :
    x ∈ rescale r T ↔ r * x ∈ T ∧ x ∈ Icc 0 1 := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    change t ∈ T ∩ Icc 0 r at ht
    exact ⟨by simpa [mul_div_cancel₀ _ hr.ne'] using ht.1,
      div_nonneg ht.2.1 hr.le, (div_le_one₀ hr).mpr ht.2.2⟩
  · rintro ⟨ht, hx⟩
    exact ⟨r * x, ⟨ht, mul_nonneg hr.le hx.1, mul_le_of_le_one_right hr.le hx.2⟩,
      by change (r * x) / r = x; rw [mul_comm, mul_div_cancel_right₀ _ hr.ne']⟩

theorem rescale_closedTarget {r : ℝ} {T : Set ℝ} (hT : IsClosedTarget T) (hr : 0 < r) :
    IsClosedTarget (rescale r T) := by
  classical
  obtain ⟨intervals, hi, rfl⟩ := hT
  let clipped := (intervals.filter fun I => decide (I.1 ≤ r)).map
    (fun I => (I.1 / r, min I.2 r / r))
  refine ⟨clipped, ?_, ?_⟩
  · intro I hI
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hI
    have hJ' := List.mem_filter.mp hJ
    exact ⟨div_nonneg (hi J hJ'.1).1 hr.le,
      (div_le_div_iff_of_pos_right hr).mpr (le_min (hi J hJ'.1).2.1 (of_decide_eq_true hJ'.2)),
      (div_le_one₀ hr).mpr (min_le_right _ _)⟩
  · ext x
    rw [mem_rescale_iff hr, mem_intervalUnion (intervals := clipped)]
    constructor
    · rintro ⟨hx, hunit⟩
      obtain ⟨I, hI, hmem⟩ := mem_intervalUnion.mp hx
      have hle : r * x ≤ r := mul_le_of_le_one_right hr.le hunit.2
      refine ⟨_, List.mem_map.mpr ⟨I, List.mem_filter.mpr ⟨hI, decide_eq_true (hmem.1.trans hle)⟩, rfl⟩,
        (div_le_iff₀ hr).mpr (by simpa [mul_comm] using hmem.1),
        (le_div_iff₀ hr).mpr (by simpa [mul_comm] using le_min hmem.2 hle)⟩
    · rintro ⟨I, hI, hmem⟩
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hI
      obtain ⟨hJ', _⟩ := List.mem_filter.mp hJ
      have hlo : J.1 ≤ r * x := by simpa [mul_comm] using (div_le_iff₀ hr).mp hmem.1
      have hhi : r * x ≤ min J.2 r := by simpa [mul_comm] using (le_div_iff₀ hr).mp hmem.2
      refine ⟨mem_intervalUnion.mpr ⟨J, hJ', hlo, hhi.trans (min_le_left _ _)⟩, ?_⟩
      exact ⟨(div_nonneg (hi J hJ').1 hr.le).trans hmem.1,
        hmem.2.trans ((div_le_one₀ hr).mpr (min_le_right _ _))⟩

theorem reflect_closedTarget {T : Set ℝ} (hT : IsClosedTarget T) : IsClosedTarget (reflect T) := by
  obtain ⟨intervals, hi, rfl⟩ := hT
  refine ⟨intervals.map (fun I => (1 - I.2, 1 - I.1)), ?_, ?_⟩
  · intro I hI
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hI
    exact ⟨sub_nonneg.mpr (hi J hJ).2.2, sub_le_sub_left (hi J hJ).2.1 _,
      sub_le_self _ (hi J hJ).1⟩
  · ext x
    rw [mem_intervalUnion]
    constructor
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨I, hI, hm⟩ := mem_intervalUnion.mp ht
      exact ⟨_, List.mem_map.mpr ⟨I, hI, rfl⟩,
        sub_le_sub_left hm.2 _, sub_le_sub_left hm.1 _⟩
    · rintro ⟨I, hI, hm⟩
      obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hI
      exact ⟨1 - x, mem_intervalUnion.mpr ⟨J, hJ, by linarith [hm.2], by linarith [hm.1]⟩, by ring⟩

theorem closedTarget_union {S T : Set ℝ} (hS : IsClosedTarget S) (hT : IsClosedTarget T) :
    IsClosedTarget (S ∪ T) := by
  obtain ⟨is, hi, rfl⟩ := hS
  obtain ⟨js, hj, rfl⟩ := hT
  refine ⟨is ++ js, ?_, ?_⟩
  · intro I hI
    exact (List.mem_append.mp hI).elim (hi I) (hj I)
  · ext x
    simp only [mem_union, mem_intervalUnion, List.mem_append, or_and_right, exists_or]

theorem residualTarget_closedTarget {r : ℝ} {T : Set ℝ} (hT : IsClosedTarget T) (hr : 0 < r) :
    IsClosedTarget (residualTarget r T) := by
  exact closedTarget_union (rescale_closedTarget hT hr) (reflect_closedTarget (rescale_closedTarget hT hr))

theorem residualTarget_symmetric (r : ℝ) (T : Set ℝ) : IsSymmetric (residualTarget r T) := by
  have aux (S U : Set ℝ) : reflect (S ∪ U) = reflect S ∪ reflect U := image_union _ _ _
  rw [IsSymmetric, residualTarget, aux, reflect_reflect, union_comm]

private def reflectionEquiv : ℝ ≃ᵐ ℝ where
  toFun := fun x => 1 - x
  invFun := fun x => 1 - x
  left_inv := fun x => by ring
  right_inv := fun x => by ring
  measurable_toFun := by change Measurable (fun x : ℝ => 1 - x); fun_prop
  measurable_invFun := by change Measurable (fun x : ℝ => 1 - x); fun_prop

private def splitInput (j : ℕ) : (Fin (j + 1) → ℝ) ≃ᵐ ℝ × (Fin j → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (0 : Fin (j + 1))).trans
    (reflectionEquiv.prodCongr (MeasurableEquiv.refl _))

private theorem splitInput_fst (j : ℕ) (u : Fin (j + 1) → ℝ) :
    (splitInput j u).1 = 1 - u 0 := rfl

private theorem splitInput_snd (j : ℕ) (u : Fin (j + 1) → ℝ) (i : Fin j) :
    (splitInput j u).2 i = u i.succ := rfl

private theorem splitInput_symm_fst (j : ℕ) (z : ℝ × (Fin j → ℝ)) :
    (splitInput j).symm z 0 = 1 - z.1 := by
  have h := congrArg Prod.fst ((splitInput j).apply_symm_apply z)
  rw [splitInput_fst] at h
  linarith

private theorem splitInput_symm_snd (j : ℕ) (z : ℝ × (Fin j → ℝ)) (i : Fin j) :
    (splitInput j).symm z i.succ = z.2 i := by
  have h := congrArg (fun q : ℝ × (Fin j → ℝ) => q.2 i) ((splitInput j).apply_symm_apply z)
  simpa only [splitInput_snd] using h

private theorem splitInput_cube (j : ℕ) :
    splitInput j ⁻¹' (Icc (0 : ℝ) 1 ×ˢ unitCube j) = unitCube (j + 1) := by
  ext u
  simp only [mem_preimage, mem_prod, mem_unitCube, splitInput_fst, splitInput_snd,
    Fin.forall_fin_succ]
  constructor <;> rintro ⟨h₀, hs⟩ <;> refine ⟨⟨?_, ?_⟩, hs⟩ <;> linarith [h₀.1, h₀.2]

private theorem measurePreserving_splitInput (j : ℕ) :
    MeasurePreserving (splitInput j) (cubeLaw (j + 1))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (cubeLaw j)) := by
  have hreflect : MeasurePreserving reflectionEquiv volume volume :=
    (volume : Measure ℝ).measurePreserving_sub_left 1
  have hpair := hreflect.prod (MeasurePreserving.id (volume : Measure (Fin j → ℝ)))
  have hsplit : MeasurePreserving (splitInput j) volume
      ((volume : Measure ℝ).prod (volume : Measure (Fin j → ℝ))) :=
    hpair.comp (volume_preserving_piFinSuccAbove (fun _ => ℝ) (0 : Fin (j + 1)))
  have hS : MeasurableSet (Icc (0 : ℝ) 1 ×ˢ unitCube j) :=
    measurableSet_Icc.prod (measurableSet_unitCube j)
  simpa only [Measure.prod_restrict, splitInput_cube, cubeLaw] using hsplit.restrict_preimage hS

/-- Fubini along the first break, including integrability of the resulting section probability. -/
theorem probability_recursion (wholeOnly : Bool) (j : ℕ) {T : Set ℝ}
    (hT : IsClosedTarget T) (hs : IsSymmetric T) :
    probability wholeOnly (j + 1) T =
      (∫ r in Icc (0 : ℝ) 1, probability wholeOnly j (residualTarget r T)) ∧
    IntegrableOn (fun r => probability wholeOnly j (residualTarget r T)) (Icc (0 : ℝ) 1) := by
  let A : Set (ℝ × (Fin j → ℝ)) :=
    (fun z => stick (j + 1) ((splitInput j).symm z)) ⁻¹' stickEvent wholeOnly (j + 1) T
  have hE := (isClosed_stickEvent wholeOnly (j + 1) hT).measurableSet
  have hA : MeasurableSet A :=
    hE.preimage ((measurable_stick (j + 1)).comp (splitInput j).symm.measurable)
  let outer := volume.restrict (Icc (0 : ℝ) 1)
  let sectionMass (r : ℝ) : ℝ≥0∞ := (cubeLaw j) (Prod.mk r ⁻¹' A)
  have hMass : Measurable sectionMass := measurable_measure_prodMk_left hA
  have hfinite (r : ℝ) : sectionMass r < ∞ := measure_lt_top _ _
  have hOuter : ∀ᵐ r ∂outer, r ∈ Ioc (0 : ℝ) 1 := by
    rw [show outer = volume.restrict (Ioc (0 : ℝ) 1) from
      Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
    exact ae_restrict_mem measurableSet_Ioc
  have hsection : (fun r => (sectionMass r).toReal) =ᵐ[outer]
      (fun r => probability wholeOnly j (residualTarget r T)) := by
    filter_upwards [hOuter] with r hr
    change ((cubeLaw j) (Prod.mk r ⁻¹' A)).toReal = _
    simp only [residualTarget, ← probability_complement]
    rw [probability, stickLaw_eq_map, map_measureReal_apply (measurable_stick j)
      (isClosed_stickEvent wholeOnly j (rescale_closedTarget hT hr.1)).measurableSet,
      measureReal_def]
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [ae_mem_cubeLaw j] with u hu
    change (stick (j + 1) ((splitInput j).symm (r, u)) ∈ stickEvent wholeOnly (j + 1) T) =
      (stick j u ∈ stickEvent wholeOnly j (rescale r T))
    have hu' : (splitInput j).symm (r, u) ∈ unitCube (j + 1) := by
      rw [mem_unitCube, Fin.forall_fin_succ, splitInput_symm_fst]
      refine ⟨⟨by linarith [hr.2], by linarith [hr.1]⟩, fun i => ?_⟩
      rw [splitInput_symm_snd]
      exact mem_unitCube.mp hu i
    have hTail : (fun i : Fin j => (splitInput j).symm (r, u) i.succ) = u :=
      funext (splitInput_symm_snd j (r, u))
    have hhead : 1 - (splitInput j).symm (r, u) 0 = r := by rw [splitInput_symm_fst]; ring
    have hh := stickEvent_stick_succ_iff (wholeOnly := wholeOnly) hs hu' (hhead.symm ▸ hr.1)
    rw [hTail, hhead] at hh
    exact propext hh
  have hintegrable : Integrable (fun r => (sectionMass r).toReal) outer := by
    refine IntegrableOn.of_bound (μ := volume) (s := Icc (0 : ℝ) 1)
      (by simp [Real.volume_Icc]) hMass.ennreal_toReal.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact (measureReal_mono (subset_univ (Prod.mk r ⁻¹' A))).trans_eq probReal_univ
  refine ⟨?_, hintegrable.congr hsection⟩
  have hpre : splitInput j ⁻¹' A = stick (j + 1) ⁻¹' stickEvent wholeOnly (j + 1) T := by
    ext u
    simp [A]
  rw [probability, stickLaw_eq_map, map_measureReal_apply (measurable_stick (j + 1)) hE,
    ← hpre, measureReal_def, (measurePreserving_splitInput j).measure_preimage hA.nullMeasurableSet,
    Measure.prod_apply hA]
  change (∫⁻ r, sectionMass r ∂outer).toReal = _
  rw [← integral_toReal hMass.aemeasurable (Filter.Eventually.of_forall hfinite)]
  exact integral_congr_ae hsection

theorem p_recursion (j : ℕ) {T : Set ℝ} (hT : IsClosedTarget T) (hs : IsSymmetric T) :
    p (j + 1) T = ∫ r in Icc (0 : ℝ) 1, p j (residualTarget r T) := by
  simpa only [probability_true] using (probability_recursion true j hT hs).1

theorem q_recursion (j : ℕ) {T : Set ℝ} (hT : IsClosedTarget T) (hs : IsSymmetric T) :
    q (j + 1) T = ∫ r in Icc (0 : ℝ) 1, q j (residualTarget r T) :=
  (probability_recursion false j hT hs).1

theorem p_residual_integrable (j : ℕ) {T : Set ℝ} (hT : IsClosedTarget T) (hs : IsSymmetric T) :
    IntegrableOn (fun r => p j (residualTarget r T)) (Icc (0 : ℝ) 1) := by
  simpa only [probability_true] using (probability_recursion true j hT hs).2

theorem q_residual_integrable (j : ℕ) {T : Set ℝ} (hT : IsClosedTarget T) (hs : IsSymmetric T) :
    IntegrableOn (fun r => q j (residualTarget r T)) (Icc (0 : ℝ) 1) :=
  (probability_recursion false j hT hs).2

end

end LeastPrime

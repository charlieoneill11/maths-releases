import LeastPrime.StickRecursion
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Absolute continuity of the stick law and the null frontiers of the two events. -/

namespace LeastPrime

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

private def prefixRemainder {j : ℕ} (v : Fin j → ℝ) (i : Fin j) : ℝ :=
  1 - ∑ k ∈ Finset.univ.filter (· < i), v k

private theorem prefixRemainder_zero {j : ℕ} (v : Fin (j + 1) → ℝ) :
    prefixRemainder v 0 = 1 := by simp [prefixRemainder, Fin.not_lt_zero]

private theorem prefixRemainder_stick_succ {j : ℕ} (u : Fin (j + 1) → ℝ) (i : Fin j) :
    prefixRemainder (stick (j + 1) u) i.succ =
      (1 - u 0) * prefixRemainder (stick j (fun k => u k.succ)) i := by
  simp only [prefixRemainder, Finset.sum_filter, Fin.sum_univ_succ,
    if_pos (Fin.succ_pos i), Fin.succ_lt_succ_iff, stick_succ_zero, stick_succ_apply]
  rw [mul_sub, mul_one, Finset.mul_sum]
  simp_rw [mul_ite, mul_zero]
  ring

private theorem prefixRemainder_stick_pos {j : ℕ} (u : Fin j → ℝ)
    (hu : ∀ i, u i < 1) (i : Fin j) : 0 < prefixRemainder (stick j u) i := by
  induction j with
  | zero => exact Fin.elim0 i
  | succ j ih =>
    cases i using Fin.cases with
    | zero => simp [prefixRemainder_zero]
    | succ i =>
      rw [prefixRemainder_stick_succ]
      exact mul_pos (sub_pos.mpr (hu 0)) (ih _ (fun k => hu k.succ) i)

private theorem stick_eq_mul_prefixRemainder {j : ℕ} (u : Fin j → ℝ) (i : Fin j) :
    stick j u i = u i * prefixRemainder (stick j u) i := by
  induction j with
  | zero => exact Fin.elim0 i
  | succ j ih =>
    cases i using Fin.cases with
    | zero => simp [stick_succ_zero, prefixRemainder_zero]
    | succ i =>
      rw [stick_succ_apply, prefixRemainder_stick_succ, ih]
      ring

private def unstick (j : ℕ) (v : Fin j → ℝ) : Fin j → ℝ :=
  fun i => v i / prefixRemainder v i

private def positivePrefixes (j : ℕ) : Set (Fin j → ℝ) :=
  {v | ∀ i, 0 < prefixRemainder v i}

private theorem unstick_stick {j : ℕ} (u : Fin j → ℝ) (hu : ∀ i, u i < 1) :
    unstick j (stick j u) = u := by
  funext i
  change stick j u i / prefixRemainder (stick j u) i = u i
  conv_lhs => lhs; rw [stick_eq_mul_prefixRemainder]
  exact mul_div_cancel_right₀ _ (prefixRemainder_stick_pos u hu i).ne'

private theorem differentiableAt_unstick {j : ℕ} {v : Fin j → ℝ}
    (hv : v ∈ positivePrefixes j) : DifferentiableAt ℝ (unstick j) v := by
  apply differentiableAt_pi.mpr
  intro i
  have hnum : DifferentiableAt ℝ (fun w : Fin j → ℝ => w i) v := by fun_prop
  have hden : DifferentiableAt ℝ (fun w : Fin j → ℝ => prefixRemainder w i) v := by
    unfold prefixRemainder
    fun_prop
  change DifferentiableAt ℝ (fun w : Fin j → ℝ => w i / prefixRemainder w i) v
  simp_rw [div_eq_mul_inv]
  exact hnum.mul (hden.inv (hv i).ne')

private theorem cubeLaw_ac_volume (j : ℕ) : cubeLaw j ≪ volume :=
  Measure.absolutelyContinuous_of_le Measure.restrict_le_self

private theorem ae_cube_lt_one (j : ℕ) : ∀ᵐ u ∂(cubeLaw j), ∀ i, u i < 1 := by
  have hne : ∀ᵐ u : Fin j → ℝ ∂volume, ∀ i, u i ≠ 1 := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin j => (volume : Measure ℝ)) i).ae
      ((volume : Measure ℝ).ae_ne 1)
  filter_upwards [ae_mem_cubeLaw j, (cubeLaw_ac_volume j).ae_le hne] with u hu hu'
  intro i
  exact lt_of_le_of_ne (mem_unitCube.mp hu i).2 (hu' i)

/-- The triangular inverse maps a null set to a null set by Mathlib's Jacobian theorem.
It agrees with the inverse of stick-breaking almost everywhere on the cube. -/
theorem stickLaw_absolutelyContinuous (j : ℕ) : stickLaw j ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hnull => ?_
  rw [stickLaw_eq_map, Measure.map_apply (measurable_stick j) hs]
  let pre := stick j ⁻¹' s
  let good := {u : Fin j → ℝ | ∀ i, u i < 1}
  have heq : pre =ᵐ[cubeLaw j] (pre ∩ good : Set (Fin j → ℝ)) := by
    filter_upwards [ae_cube_lt_one j] with u hu
    exact propext ⟨fun h => ⟨h, hu⟩, And.left⟩
  have hDiff : DifferentiableOn ℝ (unstick j) (s ∩ positivePrefixes j) := fun _ hx =>
    (differentiableAt_unstick hx.2).differentiableWithinAt
  have hImage : volume (unstick j '' (s ∩ positivePrefixes j)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hDiff
      (measure_mono_null inter_subset_left hnull)
  change cubeLaw j pre = 0
  rw [measure_congr heq]
  refine measure_mono_null ?_ ((cubeLaw_ac_volume j) hImage)
  rintro u ⟨hu, hgood⟩
  exact ⟨stick j u, ⟨hu, prefixRemainder_stick_pos u hgood⟩, unstick_stick u hgood⟩

private theorem frontier_inter_null {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} {S T : Set X} (hS : μ (frontier S) = 0) (hT : μ (frontier T) = 0) :
    μ (frontier (S ∩ T)) = 0 :=
  measure_mono_null (frontier_inter_subset _ _) (measure_union_null
    (measure_mono_null inter_subset_left hS) (measure_mono_null inter_subset_right hT))

private theorem frontier_union_null {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} {S T : Set X} (hS : μ (frontier S) = 0) (hT : μ (frontier T) = 0) :
    μ (frontier (S ∪ T)) = 0 :=
  measure_mono_null (frontier_union_subset _ _) (measure_union_null
    (measure_mono_null inter_subset_left hS) (measure_mono_null inter_subset_right hT))

private theorem frontier_biUnion_null {ι X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} (is : Finset ι) (B : ι → Set X)
    (h : ∀ i ∈ is, μ (frontier (B i)) = 0) : μ (frontier (⋃ i ∈ is, B i)) = 0 := by
  classical
  induction is using Finset.induction_on with
  | empty => simp
  | insert i is hi ih =>
    rw [Finset.set_biUnion_insert]
    exact frontier_union_null (h i (Finset.mem_insert_self _ _))
      (ih (fun a ha => h a (Finset.mem_insert_of_mem ha)))

private theorem frontier_iUnion_null {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X} (B : ι → Set X) (h : ∀ i, μ (frontier (B i)) = 0) :
    μ (frontier (⋃ i, B i)) = 0 := by
  simpa only [Finset.mem_univ, iUnion_true] using
    (frontier_biUnion_null (μ := μ) Finset.univ B (fun i _ => h i))

private theorem frontier_iInter_null {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X} (B : ι → Set X) (h : ∀ i, μ (frontier (B i)) = 0) :
    μ (frontier (⋂ i, B i)) = 0 := by
  have hh := frontier_iUnion_null (μ := μ) (fun i => (B i)ᶜ) (by simpa only [frontier_compl] using h)
  rw [← compl_iInter, frontier_compl] at hh
  exact hh

private theorem frontier_preimage_Icc_null {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (ha : μ {v | f v = a} = 0) (hb : μ {v | f v = b} = 0) : μ (frontier (f ⁻¹' Icc a b)) = 0 := by
  apply measure_mono_null (hf.frontier_preimage_subset (Icc a b))
  rw [frontier_Icc hab, show ({a, b} : Set ℝ) = {a} ∪ {b} from rfl, preimage_union]
  exact measure_union_null ha hb

private theorem volume_subsetSum_level_zero_of_nonempty {j : ℕ} (S : Finset (Fin j))
    (hS : S.Nonempty) (t : ℝ) : volume {v | subsetSum S v = t} = 0 := by
  classical
  let L : (Fin j → ℝ) →ₗ[ℝ] ℝ := ∑ i ∈ S, LinearMap.proj i
  let A := (affineSpan ℝ ({t} : Set ℝ)).comap L.toAffineMap
  have hA (v : Fin j → ℝ) : v ∈ A ↔ subsetSum S v = t := by
    rw [AffineSubspace.mem_comap, AffineSubspace.mem_affineSpan_singleton]
    simp [L, subsetSum, LinearMap.sum_apply]
  have hEq : {v | subsetSum S v = t} = (A : Set (Fin j → ℝ)) := by
    ext v
    exact (hA v).symm
  rw [hEq]
  apply Measure.addHaar_affineSubspace
  intro hAll
  have hAll' (v : Fin j → ℝ) : subsetSum S v = t :=
    (hA v).mp (by rw [hAll]; exact AffineSubspace.mem_top ℝ _ _)
  have hzero : t = 0 := by simpa [subsetSum] using (hAll' 0).symm
  obtain ⟨i, hi⟩ := hS
  let v : Fin j → ℝ := fun k => if k = i then 1 else 0
  have hone : subsetSum S v = 1 := by
    unfold subsetSum
    rw [Finset.sum_eq_single_of_mem i hi (by intro b _ hb; simp [v, hb])]
    simp [v]
  exact one_ne_zero (hone.symm.trans ((hAll' v).trans hzero))

private theorem volume_subsetSum_level_zero {j : ℕ} (S : Finset (Fin j)) {t : ℝ}
    (ht : t ≠ 0) : volume {v | subsetSum S v = t} = 0 := by
  by_cases hS : S.Nonempty
  · exact volume_subsetSum_level_zero_of_nonempty S hS t
  · have hE : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [hE, subsetSum, Ne.symm ht]

private theorem volume_residualSum_level_zero {j : ℕ} (S : Finset (Fin j)) {t : ℝ}
    (ht : t < 1) : volume {v | subsetSum S v + remainder v = t} = 0 := by
  have hEq : {v | subsetSum S v + remainder v = t} = {v | subsetSum Sᶜ v = 1 - t} := by
    ext v
    have hsum := Finset.sum_compl_add_sum S v
    change subsetSum Sᶜ v + subsetSum S v = _ at hsum
    change subsetSum S v + remainder v = t ↔ subsetSum Sᶜ v = 1 - t
    unfold remainder
    constructor <;> intro h <;> linarith
  rw [hEq]
  exact volume_subsetSum_level_zero _ (sub_pos.mpr ht).ne'

theorem volume_frontier_simplex_null (j : ℕ) : volume (frontier (simplex j)) = 0 := by
  have hEq : simplex j = (⋂ i : Fin j, (fun v : Fin j → ℝ => v i) ⁻¹' Icc 0 1) ∩
      {v | subsetSum Finset.univ v ≤ 1} := by
    ext v
    simp [simplex, subsetSum]
  rw [hEq]
  apply frontier_inter_null
  · apply frontier_iInter_null
    intro i
    have hcoord (t : ℝ) : volume {v : Fin j → ℝ | v i = t} = 0 := by
      rw [volume_pi]
      exact Measure.pi_eval_preimage_null (fun _ : Fin j => (volume : Measure ℝ)) (i := i) (s := {t}) (measure_singleton _)
    exact frontier_preimage_Icc_null (continuous_apply i) zero_le_one (hcoord 0) (hcoord 1)
  · apply measure_mono_null (frontier_le_subset_eq (continuous_subsetSum _) continuous_const)
    exact volume_subsetSum_level_zero _ one_ne_zero

private theorem frontier_intervalUnion_preimage_null {j : ℕ} {f : (Fin j → ℝ) → ℝ}
    (hf : Continuous f) (intervals : List (ℝ × ℝ)) (hI : ∀ I ∈ intervals, I.1 ≤ I.2)
    (hEnds : ∀ I ∈ intervals, volume {v | f v = I.1} = 0 ∧ volume {v | f v = I.2} = 0) :
    volume (frontier (f ⁻¹' intervalUnion intervals)) = 0 := by
  classical
  have hEq : f ⁻¹' intervalUnion intervals = ⋃ I ∈ intervals.toFinset, f ⁻¹' Icc I.1 I.2 := by
    ext v
    simp only [mem_preimage, mem_intervalUnion, mem_iUnion, exists_prop, List.mem_toFinset]
  rw [hEq]
  exact frontier_biUnion_null intervals.toFinset _ fun I hi =>
    frontier_preimage_Icc_null hf (hI I (List.mem_toFinset.mp hi))
      (hEnds I (List.mem_toFinset.mp hi)).1 (hEnds I (List.mem_toFinset.mp hi)).2

/-- The endpoint-only event has null frontier. The intersection with the simplex contributes its
own null frontier, in addition to all target endpoint hyperplanes. -/
theorem stickLaw_frontier_E_null {j : ℕ} (_hj : 0 < j) {T : Set ℝ} (hT : HasInteriorEndpoints T) :
    stickLaw j (frontier (E j T)) = 0 := by
  apply stickLaw_absolutelyContinuous
  obtain ⟨intervals, hi, rfl⟩ := hT
  rw [← stickEvent_true, eventTrue_eq]
  apply frontier_inter_null (volume_frontier_simplex_null j)
  apply frontier_iUnion_null
  intro S
  have hI (I : ℝ × ℝ) (hI : I ∈ intervals) := (hi I hI).2.1
  apply frontier_union_null
  · exact frontier_intervalUnion_preimage_null (continuous_subsetSum S) intervals hI fun I hI =>
      ⟨volume_subsetSum_level_zero S (hi I hI).1.ne',
        volume_subsetSum_level_zero S ((hi I hI).1.trans_le (hi I hI).2.1).ne'⟩
  · exact frontier_intervalUnion_preimage_null
      ((continuous_subsetSum S).add (continuous_remainder j)) intervals hI fun I hI =>
      ⟨volume_residualSum_level_zero S ((hi I hI).2.1.trans_lt (hi I hI).2.2),
        volume_residualSum_level_zero S (hi I hI).2.2⟩

/-- The interval-remainder event has null frontier by the same simplex and hyperplane bounds. -/
theorem stickLaw_frontier_F_null {j : ℕ} (_hj : 0 < j) {T : Set ℝ} (hT : HasInteriorEndpoints T) :
    stickLaw j (frontier (F j T)) = 0 := by
  classical
  apply stickLaw_absolutelyContinuous
  obtain ⟨intervals, hi, rfl⟩ := hT
  rw [← stickEvent_false, eventFalse_eq j intervals (fun I hI => (hi I hI).2.1)]
  apply frontier_inter_null (volume_frontier_simplex_null j)
  apply frontier_iUnion_null
  intro S
  let region (I : ℝ × ℝ) : Set (Fin j → ℝ) :=
    {v | subsetSum S v ≤ I.2} ∩ {v | I.1 ≤ subsetSum S v + remainder v}
  change volume (frontier (⋃ I ∈ intervals, region I)) = 0
  have hEq : (⋃ I ∈ intervals, region I) = ⋃ I ∈ intervals.toFinset, region I := by
    ext v
    simp only [mem_iUnion, exists_prop, List.mem_toFinset]
  rw [hEq]
  apply frontier_biUnion_null
  intro I hI
  have hI' := hi I (List.mem_toFinset.mp hI)
  apply frontier_inter_null
  · apply measure_mono_null (frontier_le_subset_eq (continuous_subsetSum S) continuous_const)
    exact volume_subsetSum_level_zero S (hI'.1.trans_le hI'.2.1).ne'
  · apply measure_mono_null (frontier_le_subset_eq continuous_const
      ((continuous_subsetSum S).add (continuous_remainder j)))
    simpa only [eq_comm (a := I.1)] using volume_residualSum_level_zero S (hI'.2.1.trans_lt hI'.2.2)

end

end LeastPrime

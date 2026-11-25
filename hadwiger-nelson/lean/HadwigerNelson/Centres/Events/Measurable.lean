import HadwigerNelson.Centres.Events.Definitions
import HadwigerNelson.Wave.Holes.Sections
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace HadwigerNelson.Centres
open Set MeasureTheory
noncomputable section

private theorem rotate_continuous (v : Plane) : Continuous (fun θ => Placement.rotate θ v) := by
  unfold Placement.rotate
  fun_prop

theorem candidate_measurable (X D : Finset Plane) (p : Profile) (v u : Plane) :
    MeasurableSet {θ : ℝ | candidate X D p θ v u} := by
  let g (t : ℝ) := dist u v • Wave.point (-Real.sin t) (Real.cos t)
  let limit := cone p (chord u v)
  have cont : Continuous g := by unfold g; fun_prop
  have comp : IsCompact (g '' Icc (-limit) limit) := isCompact_Icc.image cont
  have angles := (rotate_continuous (u-v)).measurable comp.isClosed.measurableSet
  by_cases fixed : orientation X D v u ∧ minorArc X u v ∧ chord u v ∈ Icc δR (245/1000)
  · convert angles using 1
    ext θ
    simp only [candidate,mem_setOf_eq,mem_preimage,mem_image,mem_Icc,aligned,g,limit,abs_le]
    constructor
    · rintro ⟨_,_,_,t,ht,e⟩
      exact ⟨t,ht,e.symm⟩
    · rintro ⟨t,ht,e⟩
      exact ⟨fixed.1,fixed.2.1,fixed.2.2,t,ht,e.symm⟩
  · have empty : {θ : ℝ | candidate X D p θ v u} = ∅ := by
      ext θ
      simp only [candidate,mem_setOf_eq,mem_empty_iff_false,iff_false]
      tauto
    rw [empty]
    exact MeasurableSet.empty

/-- The unsigned offset from the upward direction for a rotated edge. -/
def verticalOffset (v u : Plane) (θ : ℝ) : ℝ :=
  Real.arccos (Placement.rotate θ (u-v) 1 / dist u v)

theorem continuous_verticalOffset (v u : Plane) : Continuous (verticalOffset v u) := by
  unfold verticalOffset
  exact Real.continuous_arccos.comp (((PiLp.continuous_apply 2 _ 1).comp (rotate_continuous (u-v))).div_const _)

theorem cone_le_pi (p : Profile) (l : ℝ) : cone p l < Real.pi := by
  unfold cone
  split <;> exact (min_le_left ..).trans_lt (by linarith [Real.pi_gt_three])

theorem offset_of_aligned {v u : Plane} (ne : u ≠ v) {p : Profile} {l θ t : ℝ}
    (ht : |t| ≤ cone p l) (a : aligned θ t v u) : verticalOffset v u θ = |t| := by
  have eq := congrArg (fun v : Plane => v 1) a
  change Placement.rotate θ (u-v) 1 = dist u v * Real.cos t at eq
  rw [verticalOffset,eq,mul_div_cancel_left₀ _ (dist_ne_zero.mpr ne)]
  rw [← Real.cos_abs t,Real.arccos_cos (abs_nonneg _) (ht.trans (cone_le_pi p l).le)]

theorem smallRegion_abs (W : Wave.Datum) (p : Profile) (l t : ℝ) :
    smallRegion W p l |t| = smallRegion W p l t := by
  simp only [smallRegion,angleBin,abs_abs]

private theorem small_measurable (W : Wave.Datum) (p : Profile) (l : ℝ)
    (f : Placement.Sample → Plane) (hf : Continuous f)
    (a : Placement.Sample → ℝ) (ha : Continuous a) :
    MeasurableSet {ω | f ω ∈ smallRegion W p l (a ω)} := by
  have hi : Measurable fun ω => angleBin p l (a ω) := by
    unfold angleBin
    fun_prop
  change MeasurableSet {ω | ∃ k : Fin (heightBins p),
    |f ω 0| < rectangleHalfWidth W p l (angleBin p l (a ω)) k.val ∧
    |f ω 1| ∈ Icc (k.val*heightStep p) (k.val*heightStep p+heightStep p)}
  rw [setOf_exists]
  apply MeasurableSet.iUnion
  intro k
  have mh : Measurable (fun ω => rectangleHalfWidth W p l (angleBin p l (a ω)) k.val) :=
    (measurable_of_countable (fun j => rectangleHalfWidth W p l j k.val)).comp hi
  apply MeasurableSet.inter
  · exact measurableSet_lt (by fun_prop) mh
  · exact (show Measurable (fun ω => |f ω 1|) by fun_prop) measurableSet_Icc

/-- Joint measurability in angle and translation. On a candidate edge every
admissible orientation has the same absolute offset, so its small-chord
rectangle can be selected measurably from the vertical displacement. -/
theorem centreEvent_measurable (W : Wave.Datum) (X D : Finset Plane)
    (p : Profile) (v u : Plane) :
    MeasurableSet {ω : Placement.Sample | ω.2 ∈ centreEvent W X D p ω.1 v u} := by
  let l := chord u v
  let off (ω : Placement.Sample) := verticalOffset v u ω.1
  let test (i j : ℤ) (ω : Placement.Sample) : Prop :=
    let ζ := Wave.holeLatticePoint W i j
    if l ≤ 2/100 then
      Placement.place ω (midpoint u v)-ζ ∈ smallRegion W p l (off ω)
    else Placement.place ω v-ζ ∈ Wave.hole W ∧
      Placement.place ω u-ζ-Wave.point 0 2 ∈ Wave.hole W
  have eq : {ω : Placement.Sample | ω.2 ∈ centreEvent W X D p ω.1 v u} =
      (Prod.fst ⁻¹' {θ | candidate X D p θ v u}) ∩ {ω | ∃ i j, test i j ω} := by
    ext ω
    change (candidate X D p ω.1 v u ∧ _) ↔ (candidate X D p ω.1 v u ∧ _)
    apply and_congr_right
    intro c
    have ne := c.1.2.2.2.1
    obtain ⟨t,bt,at'⟩ := c.2.2.2
    apply exists_congr
    intro i
    apply exists_congr
    intro j
    by_cases small : l≤2/100
    · dsimp only [test]
      rw [if_pos small,if_pos small]
      constructor
      · rintro ⟨t',bt',at',hit⟩
        simpa only [off,offset_of_aligned ne bt' at',smallRegion_abs] using hit
      · intro hit
        refine ⟨t,bt,at',?_⟩
        simpa only [off,offset_of_aligned ne bt at',smallRegion_abs] using hit
    · change (if l ≤ 2/100 then _ else _) ↔ _
      rw [if_neg small]
      simp only [test,if_neg small]
  rw [eq]
  apply (measurable_fst (candidate_measurable X D p v u)).inter
  simp only [setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  by_cases small : l≤2/100
  · simp only [test,if_pos small]
    exact small_measurable W p l _ (by fun_prop) off ((continuous_verticalOffset v u).comp continuous_fst)
  · simp only [test,if_neg small]
    apply MeasurableSet.inter
    · exact (show Continuous (fun ω : Placement.Sample => Placement.place ω v-Wave.holeLatticePoint W i j) by fun_prop).measurable (Wave.measurable_hole W)
    · exact (show Continuous (fun ω : Placement.Sample => Placement.place ω u-Wave.holeLatticePoint W i j-Wave.point 0 2) by fun_prop).measurable (Wave.measurable_hole W)

end
end HadwigerNelson.Centres

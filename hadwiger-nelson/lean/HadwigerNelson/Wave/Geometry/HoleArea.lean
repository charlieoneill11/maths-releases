import HadwigerNelson.Wave.Geometry.PartialArea
import HadwigerNelson.Placement.Blank
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

namespace HadwigerNelson.Wave
open MeasureTheory Set
noncomputable section

/-- The closed horizontal sections of the hole have length twice the left
profile. Sections of zero thickness contribute zero Lebesgue measure. -/
theorem hole_area (W : Datum) : volume.real (hole W) = 2 * ∫ y in 0..H, W.left y := by
  let J := Icc (-W.y0) W.y0
  let K : Set (ℝ × ℝ) := {p | p.1∈J ∧ p.2∈Icc (-W.left p.1) (W.left p.1)}
  let T := regionBetween (-W.left) W.left J
  let φ : ℝ × ℝ → Plane := Placement.translationPoint ∘ Prod.swap
  have mk : MeasurableSet K := measurableSet_region_between_cc W.left_continuous.neg.measurable W.left_continuous.measurable measurableSet_Icc
  have mt : MeasurableSet T := measurableSet_regionBetween W.left_continuous.neg.measurable W.left_continuous.measurable measurableSet_Icc
  have mh : MeasurableSet (hole W) := by
    have hu : Continuous (fun z : Plane => z 0) := PiLp.continuous_apply ..
    have hy : Continuous (fun z : Plane => z 1) := PiLp.continuous_apply ..
    exact (isClosed_le hy.abs continuous_const).measurableSet.inter (isClosed_le hu.abs (W.left_continuous.comp hy)).measurableSet
  have pers : MeasurePreserving φ volume volume := Placement.translationPoint_preserves_volume.comp (Measure.measurePreserving_swap (μ:=volume) (ν:=volume))
  have eq : φ ⁻¹' hole W = K := by ext ⟨y,u⟩; simp [φ,hole,K,J,Placement.translationPoint,abs_le]
  have area := pers.measure_preimage mh.nullMeasurableSet
  rw [eq] at area
  have close : ((volume : Measure ℝ).prod volume) K = ((volume : Measure ℝ).prod volume) T := by
    rw [Measure.prod_apply mk,Measure.prod_apply mt]
    apply lintegral_congr
    intro y
    change volume {x : ℝ | y∈J ∧ x∈Icc (-W.left y) (W.left y)} = volume {x : ℝ | y∈J ∧ x∈Ioo (-W.left y) (W.left y)}
    by_cases h : y∈J
    · simp only [h,true_and,Set.setOf_mem_eq,Real.volume_Icc,Real.volume_Ioo]
    · simp [h]
  have ht : ((volume : Measure ℝ).prod volume) T = ENNReal.ofReal (∫ y in J, (W.left-(-W.left)) y) :=
    volume_regionBetween_eq_integral W.left_continuous.neg.continuousOn.integrableOn_Icc
      W.left_continuous.continuousOn.integrableOn_Icc measurableSet_Icc (fun y _ => by dsimp; linarith [(W.left_bounds y).1])
  have lo : -W.y0 ≤ W.y0 := by linarith [W.y0_bounds.1]
  have val : (∫ y in J, (W.left-(-W.left)) y) = 2*∫ y in 0..H, W.left y := by
    rw [← integral_left_hole_interval W,intervalIntegral.integral_of_le lo,← integral_Icc_eq_integral_Ioc,
      ← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by change W.left y-(-W.left y)=2*W.left y; ring)
  have nn := intervalIntegral.integral_nonneg_of_forall (μ:=volume) H_pos.le (fun y => (W.left_bounds y).1)
  rw [Measure.real,←area,show volume K=((volume : Measure ℝ).prod volume) K from rfl,close,ht,val,
    ENNReal.toReal_ofReal (by linarith)]

end
end HadwigerNelson.Wave

namespace HadwigerNelson.PartialWave
open MeasureTheory

theorem hole_area_exact : volume.real (Wave.hole datum) = 82102466727/1250000000000000 := by
  rw [Wave.hole_area,integral_left]; norm_num

end HadwigerNelson.PartialWave

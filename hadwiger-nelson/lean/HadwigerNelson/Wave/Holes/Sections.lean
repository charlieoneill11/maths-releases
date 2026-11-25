import HadwigerNelson.Wave.Holes.Definitions
import HadwigerNelson.Wave.Geometry.HoleArea

namespace HadwigerNelson.Wave
open MeasureTheory Set
open scoped ENNReal
noncomputable section

/-- Closed set whose area is the hole covariogram. -/
def holeOverlap (W : Datum) (v : Plane) : Set Plane :=
  {z | z ∈ hole W ∧ z-v ∈ hole W}

theorem measurable_hole (W : Datum) : MeasurableSet (hole W) := by
  have hu : Continuous (fun z : Plane => z 0) := PiLp.continuous_apply ..
  have hy : Continuous (fun z : Plane => z 1) := PiLp.continuous_apply ..
  exact (isClosed_le hy.abs continuous_const).measurableSet.inter
    (isClosed_le hu.abs (W.left_continuous.comp hy)).measurableSet

theorem measurable_holeOverlap (W : Datum) (v : Plane) : MeasurableSet (holeOverlap W v) :=
  (measurable_hole W).inter ((measurable_hole W).preimage (continuous_id.sub continuous_const).measurable)

/-- Horizontal or vertical sections of an intersection of two centred
intervals whose centres are separated by x. -/
theorem centred_interval_overlap (a b x : ℝ) :
    volume {u : ℝ | |u|≤a ∧ |u-x|≤b} = ENNReal.ofReal (holeSlice a b |x|) := by
  have eq : {u : ℝ | |u|≤a ∧ |u-x|≤b} = Icc (-a) a ∩ Icc (x-b) (x+b) := by
    ext u
    simp only [mem_setOf_eq,abs_le,mem_inter_iff,mem_Icc]
    constructor <;> rintro ⟨h,h₁,h₂⟩ <;> exact ⟨h,by linarith,by linarith⟩
  rw [eq,Icc_inter_Icc,Real.volume_Icc]
  simp only [holeSlice,ENNReal.ofReal_max,ENNReal.ofReal_zero,zero_le,max_eq_right]
  congr 1
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    simp only [min_def,max_def]
    split_ifs <;> linarith
  · rw [abs_of_nonpos hx]
    simp only [min_def,max_def]
    split_ifs <;> linarith

theorem holeSlice_nonneg (a b x : ℝ) : 0≤holeSlice a b x := le_max_left _ _

theorem holeSlice_antitone (a b : ℝ) : Antitone (holeSlice a b) := by
  intro u v h
  exact max_le_max_left _ (min_le_min_left _ (min_le_min_left _ (by linarith)))

private def horizontalMass (W : Datum) (x y t : ℝ) : ℝ≥0∞ := by
  classical exact if |t|≤W.y0 ∧ |t-y|≤W.y0 then
    ENNReal.ofReal (holeSlice (W.left t) (W.left (t-y)) |x|) else 0

private theorem horizontal_mass (W : Datum) (x y : ℝ) :
    volume (holeOverlap W (point x y)) = ∫⁻ t, horizontalMass W x y t := by
  let φ : ℝ × ℝ → Plane := Placement.translationPoint ∘ Prod.swap
  have mp : MeasurePreserving φ volume volume :=
    Placement.translationPoint_preserves_volume.comp (Measure.measurePreserving_swap (μ:=volume) (ν:=volume))
  have h := mp.measure_preimage (measurable_holeOverlap W (point x y)).nullMeasurableSet
  rw [← h]
  change (volume.prod volume) (φ ⁻¹' holeOverlap W (point x y)) = _
  rw [Measure.prod_apply ((measurable_holeOverlap W _).preimage mp.measurable)]
  apply lintegral_congr
  intro t
  change volume {u : ℝ | (|t| ≤ W.y0 ∧ |u| ≤ W.left t) ∧
    |t-y| ≤ W.y0 ∧ |u-x| ≤ W.left (t-y)} = _
  by_cases ht : |t|≤W.y0 ∧ |t-y|≤W.y0
  · simpa only [ht.1,ht.2,true_and,horizontalMass,if_true] using
      centred_interval_overlap (W.left t) (W.left (t-y)) x
  · rw [horizontalMass,if_neg ht]
    convert measure_empty (μ := (volume : Measure ℝ)) using 2
    ext u
    simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
    exact fun a => ht ⟨a.1.1,a.2.1⟩

theorem horizontal_mass_mono (W : Datum) (x x' y : ℝ) (h : |x| ≤ |x'|) :
    volume (holeOverlap W (point x' y)) ≤ volume (holeOverlap W (point x y)) := by
  rw [horizontal_mass,horizontal_mass]
  apply lintegral_mono
  intro t
  unfold horizontalMass
  split
  · exact ENNReal.ofReal_le_ofReal (holeSlice_antitone _ _ h)
  · exact le_rfl

theorem hole_horizontal_formula (W : Datum) (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    holeCovariogram W (point x y) = ∫ t in Ioc (y-W.y0) W.y0,
      holeSlice (W.left t) (W.left (t-y)) x := by
  let S := Icc (y-W.y0) W.y0
  let f (t : ℝ) := holeSlice (W.left t) (W.left (t-y)) x
  have fc : Continuous f := by
    have h := W.left_continuous
    dsimp [f,holeSlice]
    fun_prop (disch := assumption)
  have hi : IntegrableOn f S := fc.continuousOn.integrableOn_Icc
  have nn : 0 ≤ᵐ[volume.restrict S] f := Filter.Eventually.of_forall fun _ => holeSlice_nonneg ..
  have he : (∫⁻ t, horizontalMass W x y t) = ∫⁻ t in S, ENNReal.ofReal (f t) := by
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro t
    have mem : (|t|≤W.y0 ∧ |t-y|≤W.y0) ↔ t∈S := by
      simp only [S,abs_le,mem_Icc]
      constructor
      · intro h
        exact ⟨by linarith [h.2.1],h.1.2⟩
      · rintro ⟨a,b⟩
        exact ⟨⟨by linarith,b⟩,⟨by linarith,by linarith⟩⟩
    by_cases hm : t∈S
    · rw [horizontalMass,if_pos (mem.mpr hm),indicator_of_mem hm,abs_of_nonneg hx]
    · rw [horizontalMass,if_neg (hm ∘ mem.mp),indicator_of_notMem hm]
  change (volume (holeOverlap W (point x y))).toReal = _
  rw [horizontal_mass,he,← ofReal_integral_eq_lintegral_ofReal hi nn,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae nn)]
  exact integral_Icc_eq_integral_Ioc

end
end HadwigerNelson.Wave

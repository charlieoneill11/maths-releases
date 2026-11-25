import HadwigerNelson.Placement.Symmetry
import HadwigerNelson.Placement.Indicators

/-! The six individual colour classes have equal mean overlap for a fixed displacement. -/

open MeasureTheory HadwigerNelson.Wave
open scoped BigOperators

namespace HadwigerNelson.Placement

noncomputable section

def classProbability (W : Datum) (c : Label) (e : Plane) : ℝ :=
  ∫ t, classHit W c (translationPoint t) (translationPoint t + e) ∂translationLaw W

theorem integrable_classHit {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (W : Datum) (c : Label) {f g : α → Plane} (hf : Measurable f) (hg : Measurable g) :
    Integrable (fun a ↦ classHit W c (f a) (g a)) μ := by
  have hm := (Wave.colour_fibre_open W c).measurableSet
  apply ((integrable_const (μ := μ) (1 : ℝ)).indicator ((hm.preimage hf).inter (hm.preimage hg))).congr
  exact Filter.Eventually.of_forall fun a ↦ by
    simp only [classHit, Set.indicator, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]

private theorem class_periodic (W : Datum) (c : Label) (e : Plane) :
    PeriodicObservable W (fun z ↦ classHit W c z (z+e)) := by
  intro z v hv
  have h : z+v+e = z+e+v := by abel
  simp only [classHit, h, Wave.colour_periodic W _ v hv]

private theorem point_ext' {z z' : Plane} (h : z 0 = z' 0) (v : z 1 = z' 1) : z = z' := by
  ext i
  fin_cases i <;> assumption

/-- Reversing an unoriented segment preserves the individual colour probability. -/
theorem classProbability_reverse (W : Datum) (c : Label) (e : Plane) :
    classProbability W c (-e) = classProbability W c e := by
  have hs : Continuous (fun t ↦ -e + translationPoint t) := continuous_const.add continuous_translationPoint
  have h := translation_average_invariant W (fun z ↦ classHit W c z (z+e)) (-e)
    (class_periodic W c e)
    (integrable_classHit W c continuous_translationPoint.measurable (continuous_translationPoint.add continuous_const).measurable)
    (integrable_classHit W c hs.measurable (hs.add continuous_const).measurable)
  have h₁ (z : Plane) : -e + z + e = z := by abel
  have h₂ (z : Plane) : z + -e + e = z := by abel
  simpa only [classProbability, h₁, h₂, add_comm (-e), classHit, and_comm] using h

/-- Classes of a fixed tile shape differ by a vertical translation. -/
theorem classProbability_tau (W : Datum) (c : Label) (k : ℤ) (e : Plane) :
    classProbability W (tauLabel k c) e = classProbability W c e := by
  let s := point 0 ((k:ℝ)*H)
  have hmove (z : Plane) : s + z = tau k z := by apply point_ext' <;> simp [s,tau] <;> ring
  have hs : Continuous (fun t ↦ s + translationPoint t) := continuous_const.add continuous_translationPoint
  have h := translation_average_invariant W (fun z ↦ classHit W (tauLabel k c) z (z+e)) s
    (class_periodic W _ e)
    (integrable_classHit W _ continuous_translationPoint.measurable (continuous_translationPoint.add continuous_const).measurable)
    (integrable_classHit W _ hs.measurable (hs.add continuous_const).measurable)
  have z (t : Translation) : classHit W (tauLabel k c) (s + translationPoint t) ((s + translationPoint t) + e) =
      classHit W c (translationPoint t) (translationPoint t + e) := by
    rw [add_assoc, hmove, hmove]
    exact hit_pullback W _ _ (tau_inj k) (Wave.colour_tau W k) _ _ _
  simpa only [z, classProbability] using h.symm

/-- Vertical reflection of the segment and source colour. -/
theorem classProbability_sigma1 (W : Datum) (c : Label) (u v : ℝ) :
    classProbability W (sigma1Label c) (point u (-v)) = classProbability W c (point u v) := by
  have hs : Continuous (fun t ↦ sigma1 (translationPoint t)) := by
    change Continuous (fun t : Translation ↦ point t.1 (H-t.2))
    exact continuous_point continuous_fst (continuous_const.sub continuous_snd)
  have h := translation_average_sigma1 W (fun z ↦ classHit W (sigma1Label c) z (z + point u (-v)))
    (class_periodic W _ _)
    (integrable_classHit W _ continuous_translationPoint.measurable (continuous_translationPoint.add continuous_const).measurable)
    (integrable_classHit W _ hs.measurable (hs.add continuous_const).measurable)
  have z (t : Translation) : classHit W (sigma1Label c) (sigma1 (translationPoint t))
      (sigma1 (translationPoint t) + point u (-v)) = classHit W c (translationPoint t) (translationPoint t + point u v) := by
    have e : sigma1 (translationPoint t) + point u (-v) = sigma1 (translationPoint t + point u v) := by
      apply point_ext' <;> simp [sigma1] <;> ring
    rw [e]
    exact hit_pullback W _ _ sigma1_inj (Wave.colour_sigma1 W) _ _ _
  simpa only [z, classProbability] using h.symm

/-- Horizontal reflection exchanges the two tile shapes. -/
theorem classProbability_sigma2 (W : Datum) (c : Label) (u v : ℝ) :
    classProbability W (sigma2Label c) (point (-u) v) = classProbability W c (point u v) := by
  have hs : Continuous (fun t ↦ sigma2 (translationPoint t)) := by
    change Continuous (fun t : Translation ↦ point (-t.1) t.2)
    exact continuous_point continuous_fst.neg continuous_snd
  have h := translation_average_sigma2 W (fun z ↦ classHit W (sigma2Label c) z (z + point (-u) v))
    (class_periodic W _ _)
    (integrable_classHit W _ continuous_translationPoint.measurable (continuous_translationPoint.add continuous_const).measurable)
    (integrable_classHit W _ hs.measurable (hs.add continuous_const).measurable)
  have z (t : Translation) : classHit W (sigma2Label c) (sigma2 (translationPoint t))
      (sigma2 (translationPoint t) + point (-u) v) = classHit W c (translationPoint t) (translationPoint t + point u v) := by
    have e : sigma2 (translationPoint t) + point (-u) v = sigma2 (translationPoint t + point u v) := by
      apply point_ext' <;> simp [sigma2,add_comm]
    rw [e]
    exact hit_pullback W _ _ sigma2_inj (Wave.colour_sigma2 W) _ _ _
  simpa only [z, classProbability] using h.symm

private theorem base_y (W : Datum) (u v : ℝ) :
    classProbability W (false,0) (point u (-v)) = classProbability W (false,0) (point u v) := by
  simpa [sigma1Label] using classProbability_sigma1 W (false,0) u v

private theorem base_x (W : Datum) (u v : ℝ) :
    classProbability W (false,0) (point (-u) v) = classProbability W (false,0) (point u v) := by
  have he : -point u v = point (-u) (-v) := by apply point_ext' <;> simp
  rw [← base_y W (-u) v, ← he, classProbability_reverse]

theorem classProbability_eq_first (W : Datum) (c : Label) (u v : ℝ) :
    classProbability W c (point u v) = classProbability W (false,0) (point u v) := by
  obtain ⟨k,h | h⟩ := labelOrbit c
  · rw [h, classProbability_tau]
  · rw [h, classProbability_tau]
    have hs := classProbability_sigma2 W (false,0) (-u) v
    rw [neg_neg, base_x] at hs
    exact hs

theorem monoProb_eq_six (W : Datum) (u v : ℝ) : directionalMonoProb W (point u v) =
    6 * classProbability W (false,0) (point u v) := by
  have eq (x y : Plane) : sameColour W x y = ∑ c : Label, classHit W c x y :=
    sum_indicators (Wave.colour W x) (Wave.colour W y)
  unfold directionalMonoProb
  simp_rw [eq]
  have hi (c : Label) : Integrable (fun t : Translation ↦
      classHit W c (point t.1 t.2) (point t.1 t.2 + point u v)) (translationLaw W) :=
    integrable_classHit W c continuous_translationPoint.measurable
      (continuous_translationPoint.add (continuous_const (y := point u v))).measurable
  rw [integral_finset_sum Finset.univ (fun c _ ↦ hi c)]
  change (∑ c : Label, classProbability W c (point u v)) = _
  calc
    _ = ∑ _c : Label, classProbability W (false,0) (point u v) :=
      Finset.sum_congr rfl fun c _ ↦ classProbability_eq_first W c u v
    _ = _ := by norm_num [Wave.Label, Fintype.card_prod, ZMod.card, nsmul_eq_mul]

theorem directional_signs (W : Datum) (u v : ℝ) : directionalMonoProb W (point u v) =
    directionalMonoProb W (point |u| |v|) := by
  rw [monoProb_eq_six, monoProb_eq_six]
  rcases le_or_gt 0 u with hu | hu <;> rcases le_or_gt 0 v with hv | hv <;>
    simp [abs_of_nonneg, abs_of_neg, hu, hv, base_x, base_y]

end
end HadwigerNelson.Placement

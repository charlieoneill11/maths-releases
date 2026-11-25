import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import HadwigerNelson.Placement.Law
import HadwigerNelson.Placement.Period
import Mathlib.Tactic.Abel

/-! A unit segment's expected nonblank monochromatic indicator agrees with Definition 7. -/

open MeasureTheory Set

namespace HadwigerNelson.Placement

noncomputable section

theorem measurableSet_sameColour {α : Type*} [MeasurableSpace α] (W : Wave.Datum)
    {f g : α → Plane} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {a | (Wave.colour W (f a)).isSome = true ∧ Wave.colour W (f a) = Wave.colour W (g a)} := by
  have he : {a | (Wave.colour W (f a)).isSome = true ∧ Wave.colour W (f a) = Wave.colour W (g a)} =
      ⋃ c : Wave.Label, f ⁻¹' {z | Wave.colour W z = some c} ∩ g ⁻¹' {z | Wave.colour W z = some c} := by
    ext a
    simp only [Set.mem_setOf_eq, mem_iUnion, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hs, he⟩
      obtain ⟨c,hc⟩ := Option.isSome_iff_exists.mp hs
      exact ⟨c,hc,he ▸ hc⟩
    · rintro ⟨c,hc,hd⟩
      exact ⟨Option.isSome_iff_exists.mpr ⟨c,hc⟩,hc.trans hd.symm⟩
  rw [he]
  apply MeasurableSet.iUnion
  intro c
  have h := (Wave.colour_fibre_open W c).measurableSet
  exact (h.preimage hf).inter (h.preimage hg)

theorem integrable_sameColour {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (W : Wave.Datum) {f g : α → Plane} (hf : Measurable f) (hg : Measurable g) :
    Integrable (fun a ↦ sameColour W (f a) (g a)) μ := by
  apply ((integrable_const (μ := μ) (1 : ℝ)).indicator (measurableSet_sameColour W hf hg)).congr
  exact Filter.Eventually.of_forall fun a ↦ by simp only [sameColour, Set.indicator, Set.mem_setOf_eq]

theorem integral_translationLaw (W : Wave.Datum) (F : Translation → ℝ)
    (hint : Integrable F (translationLaw W)) :
    (∫ t, F t ∂translationLaw W) = (2 * W.x)⁻¹ * (3 * Wave.H)⁻¹ *
      ∫ u in 0..2 * W.x, ∫ y in 0..3 * Wave.H, F (u,y) := by
  have hx : 0 < 2 * W.x := by linarith [W.x_bounds.1]
  have hy : 0 < 3 * Wave.H := by linarith [Wave.H_pos]
  rw [translationLaw, integral_prod F hint, integral_uniformInterval hx]
  simp_rw [integral_uniformInterval hy]
  rw [intervalIntegral.integral_const_mul, mul_assoc]

private theorem ext_point {z z' : Plane} (a : z 0 = z' 0) (b : z 1 = z' 1) : z = z' := by
  ext i
  fin_cases i <;> assumption

/-- Translation invariance for a real function with the two periods of the wave. Integrability
is needed only on the fundamental rectangle and its specified translate. -/
theorem translation_average_invariant (W : Wave.Datum) (F : Plane → ℝ) (s : Plane)
    (hper : ∀ z v, v ∈ Wave.lattice W → F (z + v) = F z)
    (hi : Integrable (fun t ↦ F (translationPoint t)) (translationLaw W))
    (his : Integrable (fun t ↦ F (s + translationPoint t)) (translationLaw W)) :
    (∫ t, F (s + translationPoint t) ∂translationLaw W) =
      ∫ t, F (translationPoint t) ∂translationLaw W := by
  rw [integral_translationLaw W _ his, integral_translationLaw W _ hi]
  congr 1
  let f := fun u y ↦ F (Wave.point u y)
  have he (u y : ℝ) : s + translationPoint (u,y) = Wave.point (u+s 0) (y+s 1) := by
    apply ext_point <;> simp [translationPoint] <;> ring
  simp_rw [he]
  apply integral_staggered_translate f (2*W.x) (3*Wave.H) ((3/2)*Wave.H) (s 0) (s 1)
  · intro u y
    have e : Wave.point (u+2*W.x) (y+3/2*Wave.H) =
        Wave.point u y + Wave.latticePoint W 1 0 := by
      apply ext_point <;> simp [Wave.latticePoint]
    change F (Wave.point _ _) = F _
    rw [e]
    exact hper _ _ ((Wave.mem_lattice W _).2 ⟨1,0,rfl⟩)
  · intro u y
    have e : Wave.point u (y + 3*Wave.H) = Wave.point u y + Wave.latticePoint W 0 1 := by
      apply ext_point <;> simp [Wave.latticePoint]
    change F (Wave.point _ _) = F _
    rw [e]
    exact hper _ _ ((Wave.mem_lattice W _).2 ⟨0,1,rfl⟩)

/-- Every placed vertex sees the same blank density, for both the complete and partial waves. -/
theorem placed_blank_expectation (W : Wave.Datum) (x : Plane) :
    (∫ ω, if colour W ω x = none then (1 : ℝ) else 0 ∂law W) = blankDensity W := by
  let F := fun z ↦ if Wave.colour W z = none then (1:ℝ) else 0
  have hi {α : Type} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
      {g : α → Plane} (hg : Measurable g) : Integrable (fun t ↦ F (g t)) μ := by
    apply ((integrable_const (μ := μ) (1 : ℝ)).indicator
      ((Wave.blank_closed W).measurableSet.preimage hg)).congr
    exact Filter.Eventually.of_forall fun a ↦ by simp only [F, Set.indicator, Set.mem_preimage, Set.mem_setOf_eq]
  change (∫ ω, F (place ω x) ∂law W) = _
  rw [law, integral_prod _ (hi (μ := law W) (continuous_place x).measurable)]
  have ht (θ : ℝ) : (∫ t, F (place (θ,t) x) ∂translationLaw W) = blankDensity W := by
    apply translation_average_invariant W F (rotate θ x)
    · intro z v hv; simp only [F,Wave.colour_periodic W z v hv]
    · exact hi continuous_translationPoint.measurable
    · exact hi (continuous_const.add continuous_translationPoint).measurable
  simp_rw [ht]
  letI := uniformInterval_probability (show 0 < 2 * Real.pi by linarith [Real.pi_pos])
  simp

/-- A fixed oriented displacement has the same monochromatic probability at every initial point. -/
theorem directional_probability (W : Wave.Datum) (s e : Plane) :
    (∫ t, sameColour W (s + translationPoint t) ((s + translationPoint t) + e) ∂translationLaw W) =
      directionalMonoProb W e := by
  apply translation_average_invariant W (fun z ↦ sameColour W z (z+e)) s
  · intro z v hv
    have h : (z+v)+e = (z+e)+v := by abel
    simp only [sameColour, h, Wave.colour_periodic W _ v hv]
  · exact integrable_sameColour W continuous_translationPoint.measurable
      (continuous_translationPoint.add continuous_const).measurable
  · have hs : Continuous (fun t ↦ s + translationPoint t) := continuous_const.add continuous_translationPoint
    exact integrable_sameColour W hs.measurable (hs.add continuous_const).measurable

/-- The parameterized direction probability is integrable for any finite parameter measure
and measurable direction map. Each integrand is a bounded indicator on the product space. -/
theorem integrable_directional {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (W : Wave.Datum) {dir : α → Plane} (hdir : Measurable dir) :
    Integrable (fun a ↦ directionalMonoProb W (dir a)) μ := by
  let x := fun p : α × Translation ↦ translationPoint p.2
  have hx : Measurable x := continuous_translationPoint.measurable.comp measurable_snd
  have hi := integrable_sameColour (μ := μ.prod (translationLaw W)) W hx (hx.add (hdir.comp measurable_fst))
  exact hi.integral_prod_left

/-- The angle shift of a particular unit edge disappears under uniform angular averaging. -/
theorem edge_probability_of_direction (W : Wave.Datum) (x y : Plane) (φ : ℝ)
    (hu : ∀ θ, rotate θ y - rotate θ x = Wave.point (Real.cos (θ+φ)) (Real.sin (θ+φ))) :
    (∫ ω, sameColour W (place ω x) (place ω y) ∂law W) = meanMonoProb W := by
  have hi := integrable_sameColour (μ := law W) W (continuous_place x).measurable (continuous_place y).measurable
  rw [law, integral_prod _ hi]
  let P := fun θ ↦ directionalMonoProb W (Wave.point (Real.cos θ) (Real.sin θ))
  have hper : Function.Periodic P (2*Real.pi) := by
    intro θ
    simp [P, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have e (θ : ℝ) : (∫ t, sameColour W (place (θ,t) x) (place (θ,t) y) ∂translationLaw W) = P (θ+φ) := by
    have h (t : Translation) : place (θ,t) y =
        (rotate θ x + translationPoint t) + Wave.point (Real.cos (θ+φ)) (Real.sin (θ+φ)) := by
      rw [← hu θ]
      change rotate θ y + translationPoint t = _
      abel
    simp_rw [h]
    exact directional_probability W (rotate θ x) (Wave.point (Real.cos (θ+φ)) (Real.sin (θ+φ)))
  simp_rw [e]
  have hp : 0 < 2*Real.pi := by linarith [Real.pi_pos]
  rw [integral_uniformInterval hp, meanMonoProb, integral_uniformInterval hp,
    integral_translate_period hper φ]

end
end HadwigerNelson.Placement

import HadwigerNelson.Placement.Edge

/-! Averaging a lattice-periodic observable over the rectangle respects both coordinate reflections. -/

open MeasureTheory HadwigerNelson.Wave

namespace HadwigerNelson.Placement

noncomputable section

def PeriodicObservable (W : Datum) (F : Plane → ℝ) : Prop :=
  ∀ z v, v ∈ lattice W → F (z+v) = F z

private theorem point_ext' {z z' : Plane} (h : z 0 = z' 0) (v : z 1 = z' 1) : z = z' := by
  ext i
  fin_cases i <;> assumption

private theorem rect_periods (W : Datum) (F : Plane → ℝ) (hp : PeriodicObservable W F) :
    (∀ x y, F (point (x+2*W.x) (y+3/2*H)) = F (point x y)) ∧
    (∀ x, Function.Periodic (fun y ↦ F (point x y)) (3*H)) := by
  constructor
  · intro x y
    have e : point (x+2*W.x) (y+3/2*H) = point x y + latticePoint W 1 0 := by
      apply point_ext' <;> simp [latticePoint] <;> ring
    rw [e]
    exact hp _ _ ((mem_lattice W _).2 ⟨1,0,rfl⟩)
  · intro x y
    have e : point x (y+3*H) = point x y + latticePoint W 0 1 := by
      apply point_ext' <;> simp [latticePoint] <;> ring
    change F (point x (y+3*H)) = _
    rw [e]
    exact hp _ _ ((mem_lattice W _).2 ⟨0,1,rfl⟩)

/-- Reflecting the vertical coordinate at `H/2` preserves the average of a lattice-periodic
observable. The observable and its reflected version need only be integrable on the rectangle. -/
theorem translation_average_sigma1 (W : Datum) (F : Plane → ℝ) (hp : PeriodicObservable W F)
    (hi : Integrable (fun t ↦ F (translationPoint t)) (translationLaw W))
    (hs : Integrable (fun t ↦ F (sigma1 (translationPoint t))) (translationLaw W)) :
    (∫ t, F (sigma1 (translationPoint t)) ∂translationLaw W) =
      ∫ t, F (translationPoint t) ∂translationLaw W := by
  rw [integral_translationLaw W _ hs, integral_translationLaw W _ hi]
  simp only [translationPoint, sigma1, point_fst, point_snd]
  simp_rw [integral_reverse_period (h := (rect_periods W F hp).2 _) H]

/-- Reflecting the horizontal coordinate preserves the same average. -/
theorem translation_average_sigma2 (W : Datum) (F : Plane → ℝ) (hp : PeriodicObservable W F)
    (hi : Integrable (fun t ↦ F (translationPoint t)) (translationLaw W))
    (hs : Integrable (fun t ↦ F (sigma2 (translationPoint t))) (translationLaw W)) :
    (∫ t, F (sigma2 (translationPoint t)) ∂translationLaw W) =
      ∫ t, F (translationPoint t) ∂translationLaw W := by
  rw [integral_translationLaw W _ hs, integral_translationLaw W _ hi]
  congr 1
  let g := fun x ↦ ∫ y in 0..3*H, F (point x y)
  have hper : Function.Periodic g (2*W.x) :=
    staggered_outer_period (fun x y ↦ F (point x y)) _ _ _ (rect_periods W F hp).1 (rect_periods W F hp).2
  change (∫ u in 0..2*W.x, g (-u)) = ∫ u in 0..2*W.x, g u
  simpa only [zero_sub] using integral_reverse_period hper 0

end
end HadwigerNelson.Placement

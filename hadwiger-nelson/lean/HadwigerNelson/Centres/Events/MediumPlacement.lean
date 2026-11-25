import HadwigerNelson.Placement.HoleTranslations
import HadwigerNelson.Centres.Events.MediumDisplacement

namespace HadwigerNelson.Centres
open Wave Placement MeasureTheory Set
noncomputable section

/-- For a medium chord the translated intersection of two literal holes
is contained in the event at its actual rotation and translation. -/
theorem medium_translation_bound (W : Datum) (X D : Finset Plane) (p : Profile)
    (θ : ℝ) (v u : Plane) (hc : candidate X D p θ v u) (large : 2/100 < chord u v) :
    holeCovariogram W (rotate θ (u-v)-point 0 2)/(2*W.x*H) ≤
      (translationLaw W).real (centreEvent W X D p θ v u) := by
  let d := rotate θ (u-v)-point 0 2
  let B := holeOverlap W d
  apply translate_probability_lower W B (rotate θ u-point 0 2) _ (measurable_holeOverlap W d)
  · apply source_packing
    intro z hz
    exact ⟨hz.1.2.trans (W.left_bounds _).2.le,hz.1.1.trans W.y0_bounds.2.le⟩
  · intro τ g hz
    obtain ⟨i,j,eg⟩ := (mem_holeLattice W g).mp g.2
    rw [eg] at hz
    refine ⟨hc,i,j,?_⟩
    dsimp only
    rw [if_neg large.not_ge]
    obtain ⟨b,a⟩ := hz
    change translationPoint τ + (rotate θ u-point 0 2) - holeLatticePoint W i j∈hole W at b
    change translationPoint τ + (rotate θ u-point 0 2) - holeLatticePoint W i j - d∈hole W at a
    rw [show d=rotate θ u-rotate θ v-point 0 2 by simp only [d,rotate_sub]] at a
    constructor
    · change rotate θ v+translationPoint τ-holeLatticePoint W i j∈hole W
      convert a using 1; abel
    · change rotate θ u+translationPoint τ-holeLatticePoint W i j-point 0 2∈hole W
      convert b using 1; abel

/-- Direct physical interpretation of one nonnegative medium-sector
table entry, for every angle within its assigned bin. -/
theorem mediumTerm_translation (W : Datum) (profile : partialProfile W)
    (X D : Finset Plane) (p : Profile) (θ t : ℝ) (v u : Plane)
    (cand : candidate X D p θ v u) (large : 2/100 < chord u v) (align : aligned θ t v u)
    (fine : Bool) (i j : ℕ) (ok : Quadrature.mediumPass fine i = true)
    (ch : chord u v ≤ (Quadrature.breakpoint (i+1):ℝ))
    (ht : |t| ≤ (((j+1:ℕ)*(Quadrature.mEnd (Quadrature.breakpoint i)/Quadrature.mAngles fine):ℚ):ℝ)) :
    0 ≤ (Quadrature.mediumTerm fine i j:ℝ) ∧ (Quadrature.mediumTerm fine i j:ℝ) ≤
      (translationLaw W).real (centreEvent W X D p θ v u) := by
  simp only [Quadrature.mediumPass,Bool.and_eq_true,decide_eq_true_eq] at ok
  have pos : 0<Real.sqrt (4-dist u v^2) := lt_trans (by norm_num) large
  have ds : dist u v≤2 := by nlinarith [Real.sqrt_pos.mp pos,dist_nonneg (x:=u) (y:=v)]
  obtain ⟨hx,hy⟩ := medium_displacement_bounds ok.1.1 align ht ds ch
  let T : ℚ := (j+1 : ℕ)*(Quadrature.mEnd (Quadrature.breakpoint i)/Quadrature.mAngles fine)
  have a := Certificate.Hole.physical_sound W profile
    ((2*T:ℚ):ℝ) ((Quadrature.deficit (Quadrature.breakpoint (i+1))+T^2:ℚ):ℝ) (rotate θ (u-v)-point 0 2)
    (by simpa only [T,Rat.cast_mul,Rat.cast_ofNat] using hx) (by simpa only [T,Rat.cast_add,Rat.cast_pow] using hy)
  rw [Certificate.Hole.physical_rat] at a
  exact ⟨a.1,a.2.trans (medium_translation_bound W X D p θ v u cand large)⟩

end
end HadwigerNelson.Centres

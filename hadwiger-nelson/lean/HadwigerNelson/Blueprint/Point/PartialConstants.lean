import HadwigerNelson.Blueprint.Point.ForestDefs
import HadwigerNelson.Certificate.Hole.PackingBounds
import HadwigerNelson.Native.Point.Means
import HadwigerNelson.Native.Point.Packing
import HadwigerNelson.Proof.StarGain
import HadwigerNelson.Stars.Partial.Checked
import HadwigerNelson.Angular.Partial.Checked
import HadwigerNelson.Angular.Partial.Unique
import HadwigerNelson.Wave.Geometry.Partial
import HadwigerNelson.Wave.Geometry.PartialArea
import HadwigerNelson.Placement.Density

namespace HadwigerNelson.Certificate
open Wave Centres Forest
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The fixed 68-cell merged mesh covers both shifted knot grids of W_V.
Its integer width, slab areas and displacement bounds use directed rounding. -/
def partialOmega (_W : Wave.Datum) : ℝ → ℝ → ℝ := Hole.physical

theorem partialOmega_sound (W : Wave.Datum) (hW : partialProfile W) :
    Wave.holeEnclosure W (partialOmega W) := Hole.physical_sound W hW

/-- The exact evaluation in §9.1 uses only the left profile for the blank density. -/
theorem partial_blank_density (W : Wave.Datum) (hW : partialProfile W) :
    Placement.blankDensity W = 82102466727/1153889450307500 := by
  rw [Placement.blankDensity_eq_integral, PartialWave.integral_left_of_segments W hW.2.1 hW.2.2, hW.1]
  norm_num [Wave.H]

/-- Section 9.2 applied with the pointwise packing estimate for both collision
parameters. The two upper bounds L and T therefore exceed the printed ones. -/
theorem partialConstants (W : Wave.Datum) (hW : partialProfile W) :
    let Ω := partialOmega W
    let scale : ℝ := 10^18
    112668096940/scale ≤ unitMean Ω ∧
    16034576942481/scale ≤ lowerShortMean Ω a ∧ 3057937052494/scale ≤ lowerShortMean Ω d ∧
    packingSum Ω (fun _ => True) ≤ 150296106235/scale ∧
    packingSum Ω (fun t => d < t) ≤ 97911102803/scale ∧
    2*packingSum Ω (fun t => t ≤ d) ≤ 104770006866/scale ∧
    2*packingSum Ω (fun _ => True) ≤ 300592212470/scale ∧
    344/1000 ≤ retention Ω (cap Ω a) ∧ 761/1000 ≤ retention Ω (cap Ω d) := by
  obtain ⟨b, c, e, rr, rd⟩ := Hole.checkMeans_sound Hole.means_checked
  obtain ⟨l, t, u, j⟩ := Hole.checkPacking_sound W hW Hole.packing_checked
  exact ⟨b, c, e, l, t, u, j, rr, rd⟩

/-- Both sides of the piecewise-affine partial wave are pinned to the literal
release, including all 513 right ordinates of the angular certificate. -/
def fullPartialProfile (W : Wave.Datum) : Prop :=
  partialProfile W ∧ ∀ i : Fin 512, ∀ u ∈ Set.Icc (0:ℝ) 1,
    W.right (((i:ℝ)+u)*Wave.H/512) =
      ((1-u)*(PartialWave.rightKnots[i.val]!.2:ℝ) + u*(PartialWave.rightKnots[i.val+1]!.2:ℝ))/10^12

theorem fullPartialProfile_iff (W : Wave.Datum) :
    fullPartialProfile W ↔ Angular.Partial.Profile W ∧ W.y0 = 918/100000 := by
  constructor
  · rintro ⟨⟨hx,hy,hl⟩,hr⟩
    exact ⟨⟨hx,hl,hr⟩,hy⟩
  · rintro ⟨p,hy⟩
    exact ⟨⟨p.x,hy,p.left⟩,p.right⟩

theorem eq_partial_datum (W : Wave.Datum) (h : fullPartialProfile W) : W = PartialWave.datum := by
  obtain ⟨p,hy⟩ := (fullPartialProfile_iff W).mp h
  exact p.eq_datum hy

/-- The literal W_V constructed from the pinned data inhabits the assumptions
of all the point-probability and star estimates. -/
theorem datum_fullPartialProfile : fullPartialProfile PartialWave.datum :=
  ⟨⟨PartialWave.datum_x, PartialWave.datum_y0, PartialWave.datum_left_segment⟩,
    PartialWave.datum_right_segment⟩

theorem partial_mono_probability (W : Wave.Datum) (hW : fullPartialProfile W) :
    Placement.meanMonoProb W ≤ 102782566719698111/145001902327661557000000 := by
  exact Angular.Partial.probability_bound ((fullPartialProfile_iff W).mp hW).1

end
end HadwigerNelson.Certificate

namespace HadwigerNelson.Stars
open MeasureTheory
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Partial-wave part of Proposition 25. Relabelling the six colours by any
bijection leaves both the locked event and the same-colour count invariant. -/
theorem partial_locked (W : Wave.Datum) (hW : Certificate.fullPartialProfile W)
    (palette : Wave.Label ≃ Fin 6) (E : Finset (Plane×Plane))
    (unit : ∀ e ∈ E, dist e.1 e.2 = 1) (v : Plane) :
    (901/10^12 : ℝ)*degree E v ≤
      ∫ ω, gain E (fun x => (Placement.colour W ω x).map palette) v ∂Placement.law W := by
  rw [Certificate.eq_partial_datum W hW]
  exact Proof.gain_of_cell_score_for_palette _ palette _ PartialCheck.cellScore_lower E unit v

end
end HadwigerNelson.Stars

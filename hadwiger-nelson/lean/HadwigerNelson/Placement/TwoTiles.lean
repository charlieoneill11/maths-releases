import HadwigerNelson.Placement.Class
import HadwigerNelson.Placement.Covariogram
import HadwigerNelson.Placement.TileEvent
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.FieldSimp

/-! Unfolding the first colour on the fundamental rectangle. The first-quadrant event uses two
destination copies, which gives the two covariogram terms of Lemma 10. -/

open MeasureTheory HadwigerNelson.Wave Set
open scoped ENNReal

namespace HadwigerNelson.Placement

noncomputable section

def baseEvent (W : Datum) (u v : ℝ) : Set Translation :=
  {t | Wave.colour W (translationPoint t) = some (false,0) ∧
       Wave.colour W (translationPoint t + point u v) = some (false,0)}

def rectangle (W : Datum) : Set Translation := Ioc 0 (2*W.x) ×ˢ Ioc 0 (3*H)

private theorem measurable_base (W : Datum) (u v : ℝ) : MeasurableSet (baseEvent W u v) := by
  have h := (colour_fibre_open W (false,0)).measurableSet
  exact (h.preimage continuous_translationPoint.measurable).inter
    (h.preimage (continuous_translationPoint.add continuous_const).measurable)

private theorem swap_base_subset (W : Datum) {u v : ℝ} (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) :
    baseEvent W u v ∩ rectangle W ⊆ Prod.swap ⁻¹' (
      overlapRegion W.left W.right H (-u) (-v) ∪ overlapRegion W.left W.right H (2*W.x-u) (3/4-v)) := by
  rintro ⟨x,y⟩ ⟨⟨hc,hc'⟩,⟨hx,hy⟩⟩
  have ht := first_colour_in_rectangle W (point x y) (Ioc_subset_Icc_self hx) (Ioc_subset_Icc_self hy) hc
  have hb : (y,x) ∈ tileRegion W.left W.right H := ht
  rcases tile_matching_offsets W _ _ _ ht hu hv hc' with hn | hn
  · left
    refine ⟨hb, ?_⟩
    change (y- -v,x- -u) ∈ tileRegion W.left W.right H
    simpa [sub_neg_eq_add, tileRegion, regionBetween, Wave.tile] using hn
  · right
    refine ⟨hb, ?_⟩
    change (y-(3/4-v), x-(2*W.x-u)) ∈ tileRegion W.left W.right H
    change (point x y + point u v - latticePoint W 1 0) ∈ tile W at hn
    have hey : y-(3/4-v) = y+v-(3/2)*H := by unfold H; ring
    have hex : x-(2*W.x-u) = x+u-2*W.x := by ring
    simpa [hey,hex,tileRegion,regionBetween,Wave.tile,latticePoint] using hn

private theorem swap_base_eq (W : Datum) {u v : ℝ} (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) :
    baseEvent W u v ∩ rectangle W = Prod.swap ⁻¹' (
      overlapRegion W.left W.right H (-u) (-v) ∪ overlapRegion W.left W.right H (2*W.x-u) (3/4-v)) := by
  apply Set.Subset.antisymm (swap_base_subset W hu hv)
  rintro ⟨x,y⟩ (h | h)
  all_goals
    have ht : point x y ∈ Wave.tile W := h.1
    have hb := tile_coord_bounds W ht
    change (0 < x ∧ x < 1) ∧ (0 < y ∧ y < H) at hb
    refine ⟨⟨colour_on_tile W _ ht,?_⟩,⟨hb.1.1,?_⟩,⟨hb.2.1,?_⟩⟩
    rotate_left
    · change x ≤ 2*W.x
      linarith [hb.1.2, W.x_bounds.1]
    · change y ≤ 3*H
      linarith [hb.2.2,H_pos]
  · apply colour_on_tile
    have hn := h.2
    change (y- -v,x- -u) ∈ tileRegion W.left W.right H at hn
    simpa [sub_neg_eq_add, tileRegion, regionBetween, Wave.tile, translationPoint] using hn
  · let z := translationPoint (x,y)+point u v
    let p := latticePoint W 1 0
    have hz : z-p ∈ tile W := by
      have hn := h.2
      change (y-(3/4-v),x-(2*W.x-u)) ∈ tileRegion W.left W.right H at hn
      have hy : y-(3/4-v) = y+v-(3/2)*H := by unfold H; ring
      have hx : x-(2*W.x-u) = x+u-2*W.x := by ring
      simpa [z,p,translationPoint,hy,hx,tileRegion,regionBetween,Wave.tile,latticePoint] using hn
    have hp := Wave.colour_periodic W (z-p) p ((Wave.mem_lattice W p).2 ⟨1,0,rfl⟩)
    rw [sub_add_cancel] at hp
    exact hp.trans (colour_on_tile W _ hz)

private theorem overlaps_disjoint (W : Datum) (u v : ℝ) :
    Disjoint (overlapRegion W.left W.right H (-u) (-v))
      (overlapRegion W.left W.right H (2*W.x-u) (3/4-v)) := by
  apply Set.disjoint_left.mpr
  rintro ⟨y,x⟩ ha hb
  have h1 : point (x- -u) (y- -v) ∈ tile W := ha.2
  have h2 : point (x-(2*W.x-u)) (y-(3/4-v)) ∈ tile W := hb.2
  have e1 := (tile_coord_bounds W h1).1.2
  have e2 := (tile_coord_bounds W h2).1.1
  change x- -u < 1 at e1
  change 0 < x-(2*W.x-u) at e2
  linarith [W.x_bounds.1]

private theorem overlap_finite (W : Datum) (u v : ℝ) :
    ((volume : Measure ℝ).prod volume) (overlapRegion W.left W.right H u v) < ∞ := by
  have h : overlapRegion W.left W.right H u v ⊆ Ioo 0 H ×ˢ Ioo 0 (1 : ℝ) := by
    intro t ht
    have hz : point t.2 t.1 ∈ Wave.tile W := ht.1
    have hb := tile_coord_bounds W hz
    exact ⟨hb.2,hb.1⟩
  refine lt_of_le_of_lt (measure_mono h) ?_
  rw [Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem baseProbability_rect (W : Datum) (u v : ℝ) :
    classProbability W (false,0) (point u v) = (2*W.x)⁻¹ * (3*H)⁻¹ *
      ((volume : Measure ℝ).prod volume).real (baseEvent W u v ∩ rectangle W) := by
  have he : classProbability W (false,0) (point u v) = (translationLaw W).real (baseEvent W u v) := by
    unfold classProbability
    calc
      _ = ∫ t, (baseEvent W u v).indicator (1 : Translation → ℝ) t ∂translationLaw W := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t ↦ by
          simp only [classHit, baseEvent, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
      _ = _ := integral_indicator_one (measurable_base W u v)
  rw [he, translationLaw, uniformInterval, uniformInterval, Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.prod_restrict, measureReal_ennreal_smul_apply, measureReal_ennreal_smul_apply,
    measureReal_restrict_apply (measurable_base W u v)]
  have hx : 0 ≤ 2*W.x := by linarith [W.x_bounds.1]
  have hy : 0 ≤ 3*H := by linarith [H_pos]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hx, ENNReal.toReal_ofReal hy, rectangle, mul_assoc]

/-- The pair probability for a displacement in the first unit quadrant equals the sum of
the two physical tile overlaps of Lemma 10, normalized by their source area. -/
theorem monoProb_eq_covariograms (W : Datum) {u v : ℝ} (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) :
    directionalMonoProb W (point u v) =
      (tileCovariogram W.left W.right H u v + tileCovariogram W.left W.right H (2*W.x-u) |3/4-v|) /
        (W.x * H) := by
  let A := overlapRegion W.left W.right H (-u) (-v)
  let B := overlapRegion W.left W.right H (2*W.x-u) (3/4-v)
  let μ := (volume : Measure ℝ).prod (volume : Measure ℝ)
  have hm : MeasurableSet (A ∪ B) := (measurable_overlap W _ _).union (measurable_overlap W _ _)
  have ha : μ.real (baseEvent W u v ∩ rectangle W) = μ.real A + μ.real B := calc
    _ = μ.real (Prod.swap ⁻¹' (A ∪ B)) := congrArg μ.real (swap_base_eq W hu hv)
    _ = μ.real (A ∪ B) := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).measureReal_preimage hm.nullMeasurableSet
    _ = _ := measureReal_union (overlaps_disjoint W u v) (measurable_overlap W _ _)
      (overlap_finite W _ _).ne (overlap_finite W _ _).ne
  change μ.real (baseEvent W u v ∩ rectangle W) =
    tileCovariogram W.left W.right H (-u) (-v) + tileCovariogram W.left W.right H (2*W.x-u) (3/4-v) at ha
  have hx : 0 < W.x := by linarith [W.x_bounds.1]
  have hd : 0 ≤ 2*W.x-u := by linarith [W.x_bounds.1, hu.2]
  rw [tileCovariogram_neg, tileCovariogram_abs W (2*W.x-u) (3/4-v), abs_of_nonneg hd] at ha
  rw [monoProb_eq_six,baseProbability_rect]
  have factor : 6 * ((2*W.x)⁻¹ * (3*H)⁻¹) = (W.x*H)⁻¹ := by field_simp [hx.ne', H_pos.ne'] <;> ring
  rw [← mul_assoc, factor, div_eq_inv_mul]
  rw [ha]

end
end HadwigerNelson.Placement

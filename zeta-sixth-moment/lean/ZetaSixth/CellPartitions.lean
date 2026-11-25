import ZetaSixth.LinearBoundaries
import ZetaSixth.VolumeCoordinates
import Mathlib.Tactic.NormNum

/-!
# Weighted mass of finite cell partitions

The cells are described in short-sum coordinates. The intended regions can omit
affine boundary planes, which have zero volume and zero weighted mass.
-/

namespace ZetaSixth

open Filter MeasureTheory Set

namespace Cell

/-- The union of a finite list of cells in short-sum coordinates. -/
noncomputable def union : List Cell → Set Point
  | [] => ∅
  | c :: cs => c.set ∪ union cs

theorem mem_union {p : Point} {cs : List Cell} :
    p ∈ union cs ↔ ∃ c ∈ cs, p ∈ c.set := by
  induction cs with
  | nil => simp [union]
  | cons c cs ih =>
    simp only [union, Set.mem_union, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨d, hd, hp⟩)
      · exact ⟨c, Or.inl rfl, h⟩
      · exact ⟨d, Or.inr hd, hp⟩
    · rintro ⟨d, hd | hd, hp⟩
      · exact Or.inl (hd ▸ hp)
      · exact Or.inr ⟨d, hd, hp⟩

/-- Cells in separated short-sum intervals are disjoint. -/
theorem disjoint_of_kHi_le_kLo {c d : Cell} (h : (c.kHi : ℝ) ≤ d.kLo) :
    Disjoint c.set d.set := by
  rw [Set.disjoint_left]
  intro p hp hq
  exact (not_lt_of_ge (h.trans hq.1.1.le)) hp.1.2

private theorem measurableSet_union (cs : List Cell) : MeasurableSet (union cs) := by
  induction cs with
  | nil => exact MeasurableSet.empty
  | cons c cs ih => exact c.measurableSet_set.union ih

/-- Exact rational sum of the short-sum coordinate integrals. -/
def massSum (cs : List Cell) : ℚ := (cs.map fun c => c.integrate shortSumDensityPoly).sum

private theorem integral_nonneg (c : Cell) (hc : c.Ordered) :
    0 ≤ c.integrate shortSumDensityPoly := by
  have h : 0 ≤ (c.integrate shortSumDensityPoly : ℝ) := by
    rw [← c.integral_eq shortSumDensityPoly hc]
    apply MeasureTheory.integral_nonneg
    intro p
    rw [eval_shortSumDensityPoly]
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  exact_mod_cast h

private theorem massSum_nonneg (cs : List Cell) (h : ∀ c ∈ cs, c.Ordered) :
    0 ≤ massSum cs := by
  induction cs with
  | nil => simp [massSum]
  | cons c cs ih =>
    exact add_nonneg (c.integral_nonneg (h c (by simp)))
      (ih fun d hd => h d (List.mem_cons_of_mem _ hd))

/-- An ordered disjoint collection integrates to the sum of its computed cell masses. -/
theorem mu_union (cs : List Cell)
    (ho : ∀ c ∈ cs, c.Ordered)
    (hs : shortCoordinates ⁻¹' union cs ⊆ Ω)
    (hp : cs.Pairwise fun c d => Disjoint c.set d.set) :
    μ (shortCoordinates ⁻¹' union cs) = ENNReal.ofReal (massSum cs : ℝ) := by
  induction cs with
  | nil => simp [union, massSum]
  | cons c cs ih =>
    have hhead : shortCoordinates ⁻¹' c.set ⊆ Ω :=
      fun _ h => hs (Or.inl h)
    have htail : shortCoordinates ⁻¹' union cs ⊆ Ω :=
      fun _ h => hs (Or.inr h)
    have horder : ∀ d ∈ cs, d.Ordered := fun d hd => ho d (List.mem_cons_of_mem _ hd)
    obtain ⟨hdisj, hpTail⟩ := List.pairwise_cons.mp hp
    have hd : Disjoint (shortCoordinates ⁻¹' c.set) (shortCoordinates ⁻¹' union cs) := by
      rw [Set.disjoint_left]
      intro p hc hcs
      obtain ⟨d, hd, hpd⟩ := mem_union.mp hcs
      exact (Set.disjoint_left.mp (hdisj d hd)) hc hpd
    change μ (shortCoordinates ⁻¹' c.set ∪ shortCoordinates ⁻¹' union cs) = _
    rw [measure_union hd (shortCoordinates.measurable (measurableSet_union cs)),
      mu_shortCell c (ho c (by simp)) hhead, ih horder htail hpTail]
    change ENNReal.ofReal (c.integrate shortSumDensityPoly : ℝ) +
      ENNReal.ofReal (massSum cs : ℝ) =
        ENNReal.ofReal ((c.integrate shortSumDensityPoly + massSum cs : ℚ) : ℝ)
    rw [Rat.cast_add, ENNReal.ofReal_add]
    · exact_mod_cast c.integral_nonneg (ho c (by simp))
    · exact_mod_cast massSum_nonneg cs horder

end Cell

theorem mu_congr_volume {s t : Set Point} (h : s =ᵐ[volume] t) : μ s = μ t := by
  have hac : μ ≪ (volume : Measure Point) :=
    (withDensity_absolutelyContinuous _ _).trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  exact measure_congr (hac.ae_eq h)

theorem ae_short_coordinate_ne (d : ℝ) : ∀ᵐ p : Point ∂volume, p.1 ≠ d := by
  simpa only [one_mul, zero_mul, add_zero] using ae_ne_coord_level 1 0 0 d (by norm_num)

theorem ae_second_coordinate_ne (a b : ℝ) : ∀ᵐ p : Point ∂volume, p.2.1 ≠ a + b * p.1 := by
  filter_upwards [ae_ne_coord_level b (-1) 0 (-a) (by norm_num)] with p h
  intro heq
  apply h
  linarith

theorem ae_third_coordinate_ne (a b c : ℝ) :
    ∀ᵐ p : Point ∂volume, p.2.2 ≠ a + b * p.1 + c * p.2.1 := by
  filter_upwards [ae_ne_coord_level b c (-1) (-a) (by norm_num)] with p h
  intro heq
  apply h
  linarith

/-- Transfer an almost-everywhere partition in the short-sum coordinates back to the chamber. -/
theorem mu_from_cell_partition {s : Set Point} (cs : List Cell)
    (h : (shortCoordinates.symm ⁻¹' s : Set Point) =ᵐ[volume] Cell.union cs)
    (ho : ∀ c ∈ cs, c.Ordered)
    (hs : shortCoordinates ⁻¹' Cell.union cs ⊆ Ω)
    (hp : cs.Pairwise fun c d => Disjoint c.set d.set) :
    μ s = ENNReal.ofReal (Cell.massSum cs : ℝ) := by
  have hpre := shortCoordinates_measurePreserving.quasiMeasurePreserving.preimage_ae_eq h
  have heq : s =ᵐ[volume] (shortCoordinates ⁻¹' Cell.union cs : Set Point) := by
    filter_upwards [hpre] with p hp
    change (shortCoordinates.symm (shortCoordinates p) ∈ s) =
      (p ∈ shortCoordinates ⁻¹' Cell.union cs) at hp
    simpa only [MeasurableEquiv.symm_apply_apply] using hp
  exact (mu_congr_volume heq).trans (Cell.mu_union cs ho hs hp)

end ZetaSixth

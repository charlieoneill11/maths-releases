import ZetaSixth.CellIntegral
import ZetaSixth.RegionGeometry
import Mathlib.MeasureTheory.Group.Prod

/-!
# Volume-preserving coordinates

Reassociation and swapping preserve product volume. The short-sum coordinate map
composes these permutations with the Haar shear `(x,y) ↦ (x,x+y)`. Chamber reflection
uses the corresponding coordinate permutation, negation, and translation.
-/

namespace ZetaSixth

open MeasureTheory Set

/-- Change from `(x,y,z)` to the short-sum coordinates `(x+y,x,z)`. -/
noncomputable def shortCoordinates : Point ≃ᵐ Point where
  toFun p := (p.1 + p.2.1, p.1, p.2.2)
  invFun p := (p.2.1, p.1 - p.2.1, p.2.2)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := by fun_prop
  measurable_invFun := by fun_prop

@[simp] theorem shortCoordinates_apply (p : Point) :
    shortCoordinates p = (p.1 + p.2.1, p.1, p.2.2) := rfl

@[simp] theorem shortCoordinates_symm_apply (p : Point) :
    shortCoordinates.symm p = (p.2.1, p.1 - p.2.1, p.2.2) := rfl

private theorem reassociation_measurePreserving :
    MeasurePreserving (MeasurableEquiv.prodAssoc : ((ℝ × ℝ) × ℝ) ≃ᵐ Point)
      volume volume :=
  volume_preserving_prodAssoc

/-- The short-sum change of coordinates preserves three-dimensional product volume. -/
theorem shortCoordinates_measurePreserving : MeasurePreserving shortCoordinates volume volume := by
  let a : ((ℝ × ℝ) × ℝ) ≃ᵐ Point := MeasurableEquiv.prodAssoc
  have ha : MeasurePreserving a volume volume := reassociation_measurePreserving
  have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
    Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
  have hshear : MeasurePreserving (fun p : ℝ × ℝ => (p.1 + p.2, p.1)) volume volume :=
    hswap.comp (measurePreserving_prod_add (volume : Measure ℝ) (volume : Measure ℝ))
  exact ha.comp ((hshear.prod (MeasurePreserving.id (volume : Measure ℝ))).comp (ha.symm a))

/-- Chamber reflection as a measurable involutive equivalence of the ambient space. -/
noncomputable def reflectionCoordinates : Point ≃ᵐ Point where
  toFun := J
  invFun := J
  left_inv := J_involutive
  right_inv := J_involutive
  measurable_toFun := continuous_J.measurable
  measurable_invFun := continuous_J.measurable

@[simp] theorem reflectionCoordinates_apply (p : Point) : reflectionCoordinates p = J p := rfl

/-- Chamber reflection preserves ambient volume. -/
theorem J_volumePreserving : MeasurePreserving J volume volume := by
  let a : ((ℝ × ℝ) × ℝ) ≃ᵐ Point := MeasurableEquiv.prodAssoc
  have ha : MeasurePreserving a volume volume := reassociation_measurePreserving
  have hswap : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) volume volume :=
    Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
  have houter : MeasurePreserving (Prod.swap : (ℝ × ℝ) × ℝ → Point) volume volume :=
    Measure.measurePreserving_swap (μ := (volume : Measure (ℝ × ℝ))) (ν := (volume : Measure ℝ))
  have hreverse : MeasurePreserving (fun p : Point => (p.2.2, p.2.1, p.1)) volume volume :=
    houter.comp ((hswap.prod (MeasurePreserving.id (volume : Measure ℝ))).comp (ha.symm a))
  have hunit : MeasurePreserving (fun x : ℝ => 1 - x) volume volume := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      (measurePreserving_add_left (volume : Measure ℝ) (1 : ℝ)).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  exact (hunit.prod (hunit.prod hunit)).comp hreverse

/-- Chamber reflection preserves the restricted Lebesgue measure. -/
theorem J_measurePreserving : MeasurePreserving J chamberVolume chamberVolume := by
  have hpre : J ⁻¹' Ω = Ω := Set.ext fun _ => J_mem_Ω_iff
  simpa only [chamberVolume, hpre] using
    J_volumePreserving.restrict_preimage_emb reflectionCoordinates.measurableEmbedding Ω

/-- Chamber reflection preserves the weighted measure. -/
theorem J_muPreserving : MeasurePreserving J μ μ := by
  refine ⟨continuous_J.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply continuous_J.measurable hs, μ,
    withDensity_apply _ (continuous_J.measurable hs), withDensity_apply _ hs]
  have h := J_measurePreserving.restrict_preimage_emb reflectionCoordinates.measurableEmbedding s
  simpa only [v_comp_J] using h.lintegral_comp_emb reflectionCoordinates.measurableEmbedding
    (fun p => ENNReal.ofReal ((Nat.factorial 9 : ℝ) * v p ^ 2))

theorem mu_J_image (s : Set Point) : μ (J '' s) = μ s := by
  rw [J_involutive.image_eq_preimage_symm]
  exact J_muPreserving.measure_preimage_emb reflectionCoordinates.measurableEmbedding s

/-- The density polynomial is integrable on every subset of the chamber. -/
theorem integrableOn_density_of_subset {s : Set Point} (hsub : s ⊆ Ω) :
    IntegrableOn (fun p => (Nat.factorial 9 : ℝ) * v p ^ 2) s := by
  have hc : Continuous (fun p => (Nat.factorial 9 : ℝ) * v p ^ 2) :=
    continuous_const.mul (continuous_v.pow 2)
  let box : Set Point := Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  have hbox : IsCompact box := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  apply (hc.continuousOn.integrableOn_compact hbox).mono_set
  intro p hp
  rcases hsub hp with ⟨hx, hxy, hyz, hz⟩
  exact ⟨⟨hx.le, (hxy.trans (hyz.trans hz)).le⟩,
    ⟨(hx.trans hxy).le, (hyz.trans hz).le⟩, ⟨(hx.trans (hxy.trans hyz)).le, hz.le⟩⟩

/-- On a measurable subset of the chamber, the weighted mass is the integral of its density. -/
theorem mu_eq_ofReal_integral {s : Set Point} (hs : MeasurableSet s) (hsub : s ⊆ Ω) :
    μ s = ENNReal.ofReal (∫ p in s, (Nat.factorial 9 : ℝ) * v p ^ 2) := by
  rw [μ, withDensity_apply _ hs, chamberVolume, Measure.restrict_restrict_of_subset hsub]
  exact (ofReal_integral_eq_lintegral_ofReal (integrableOn_density_of_subset hsub)
    (Filter.Eventually.of_forall fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))).symm

/-- The chamber mass is finite. -/
theorem mu_finite : μ univ < ⊤ := by
  rw [μ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, chamberVolume]
  change (∫⁻ p in Ω, ENNReal.ofReal ((Nat.factorial 9 : ℝ) * v p ^ 2)) < ⊤
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_density_of_subset Subset.rfl)
    (Filter.Eventually.of_forall fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))]
  exact ENNReal.ofReal_lt_top

/-- The integral giving the mass of a measurable subset, in short-sum coordinates. -/
theorem mu_eq_ofReal_integral_short {s : Set Point} (hs : MeasurableSet s) (hsub : s ⊆ Ω) :
    μ s = ENNReal.ofReal (∫ p in shortCoordinates '' s, shortSumDensityPoly.eval p) := by
  rw [mu_eq_ofReal_integral hs hsub]
  congr 1
  have hchange := shortCoordinates_measurePreserving.setIntegral_image_emb
    shortCoordinates.measurableEmbedding
    (fun p => (Nat.factorial 9 : ℝ) * v (shortCoordinates.symm p) ^ 2) s
  simp only [MeasurableEquiv.symm_apply_apply] at hchange
  simpa only [eval_shortSumDensityPoly, shortCoordinates_symm_apply] using hchange.symm

/-- Exact rational mass of a chamber cell in the original coordinates. -/
theorem mu_cell (c : Cell) (h : c.Ordered) (hsub : c.set ⊆ Ω) :
    μ c.set = ENNReal.ofReal (c.integrate densityPoly : ℝ) := by
  rw [mu_eq_ofReal_integral c.measurableSet_set hsub,
    ← c.integral_eq densityPoly h]
  simp only [eval_densityPoly]

/-- Exact rational mass of a chamber cell represented in short-sum coordinates. -/
theorem mu_shortCell (c : Cell) (h : c.Ordered) (hsub : shortCoordinates ⁻¹' c.set ⊆ Ω) :
    μ (shortCoordinates ⁻¹' c.set) = ENNReal.ofReal (c.integrate shortSumDensityPoly : ℝ) := by
  rw [mu_eq_ofReal_integral_short (shortCoordinates.measurable c.measurableSet_set) hsub,
    image_preimage_eq _ shortCoordinates.surjective, c.integral_eq shortSumDensityPoly h]

end ZetaSixth

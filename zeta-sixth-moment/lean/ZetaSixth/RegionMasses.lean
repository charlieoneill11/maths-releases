import ZetaSixth.ChamberMass
import ZetaSixth.MassRecombination
import ZetaSixth.RegionCells

/-!
# Exact masses for the mixed-row region and the support ceiling

The partition lemmas identify the measured regions with disjoint cells up to null
boundaries. The numerical checks evaluate the integrated density in the kernel.
-/

namespace ZetaSixth

open MeasureTheory
open RegionCells

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem markedCells_integral : Cell.massSum markedCells = 209 / 1024 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem markedBalancedCells_integral : Cell.massSum markedBalancedCells = 62748701 / 30991570176 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem allMarkCells_integral : Cell.massSum allMarkCells =
    665446127419388501239 / 40002393722599031356416 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem twoMarkCells_integral : Cell.massSum twoMarkCells =
    1592111573351043355967 / 529288496282004750000000 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- The reflected masses in Table 1, in the printed order. -/
theorem seven_reflected_masses :
    sevenCells.map (fun c => 2 * c.integrate shortSumDensityPoly) =
      [303738701961421013 / 375042298197600000000,
       548395255530367 / 2651124843250000000,
       9090045139845151219 / 3478806019312650000000,
       1550623666362676605 / 3200621415779366111104,
       5312876028742353 / 18185348953291852904,
       905664298883259 / 869958349249567424,
       33779 / 1475789056] := by
  decide +kernel

private theorem sum_reflected_cells (cs : List Cell) :
    (cs.map (fun c => 2 * c.integrate shortSumDensityPoly)).sum = 2 * Cell.massSum cs := by
  induction cs with
  | nil => simp [Cell.massSum]
  | cons c cs ih => simp [Cell.massSum, ih, mul_add]

/-- The total reflected mass of the seven cells in Table 1. -/
theorem seven_reflected_total : 2 * Cell.massSum sevenCells =
    268755110285287452500182503673016801 / 49130135420790450741077959596000000000 := by
  rw [← sum_reflected_cells, seven_reflected_masses]
  norm_num

private theorem sevenCells_integral : Cell.massSum sevenCells =
    268755110285287452500182503673016801 / 98260270841580901482155919192000000000 := by
  linarith [seven_reflected_total]

/-- The all-marks stage gain over the exact factorable-row coefficient in Theorem 67. -/
theorem all_mark_gain_over_factorable :
    (2578241177999 / 61983140352 : ℚ) + 2 * Cell.massSum allMarkCells -
      3307268442615739142376085993 / 79479266349492187500000000 =
    446342629649862612781335389271984203 / 25646981479481579590121601562500000000 := by
  rw [allMarkCells_integral]
  norm_num

/-- The reflected contribution of the two-mark cells in Theorem 79. -/
theorem two_mark_gain : 2 * Cell.massSum twoMarkCells =
    1592111573351043355967 / 264644248141002375000000 := by
  rw [twoMarkCells_integral]
  norm_num

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lowerCeilingCells_integral : Cell.massSum lowerCeilingCells = 55 / 2048 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem ceilingBalancedCells_integral : Cell.massSum ceilingBalancedCells =
    134173355669 / 2941777950300000000 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem ceilingMixedCells_integral : Cell.massSum ceilingMixedCells =
    196813181035147418047099 / 949275554159332482383700000000 := by
  decide +kernel

theorem mu_N0 : μ N0 = ENNReal.ofReal (209 / 1024 : ℝ) := by
  rw [mu_markedCells, markedCells_integral]
  norm_num

theorem mu_N0_balanced :
    μ (N0 ∩ balanced) = ENNReal.ofReal (62748701 / 30991570176 : ℝ) := by
  rw [mu_markedBalancedCells, markedBalancedCells_integral]
  norm_num

/-- The balanced-row coefficient computed from the two marked-region masses. -/
theorem balanced_coefficient :
    (42 : ℚ) - 2 * (Cell.massSum markedCells - Cell.massSum markedBalancedCells) =
      2578241177999 / 61983140352 := by
  rw [markedCells_integral, markedBalancedCells_integral]
  norm_num

private theorem massSum_append (cs ds : List Cell) :
    Cell.massSum (cs ++ ds) = Cell.massSum cs + Cell.massSum ds := by
  simp only [Cell.massSum, List.map_append, List.sum_append]

theorem mu_N0_mixed :
    μ ((N0 ∩ FPlus) \ balanced) =
      ENNReal.ofReal (
        665446127419388501239 / 40002393722599031356416 +
        1592111573351043355967 / 529288496282004750000000 +
        268755110285287452500182503673016801 / 98260270841580901482155919192000000000 : ℝ) := by
  rw [mu_mixedCells, mixedCells, massSum_append, massSum_append,
    allMarkCells_integral, twoMarkCells_integral, sevenCells_integral]
  norm_num

private theorem mu_N0_loss :
    μ (N0 \ (balanced ∪ FPlus)) =
      μ N0 - (μ (N0 ∩ balanced) + μ ((N0 ∩ FPlus) \ balanced)) := by
  have hfinite : μ (N0 ∩ balanced) + μ ((N0 ∩ FPlus) \ balanced) ≠ ⊤ := by
    rw [mu_N0_balanced, mu_N0_mixed]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  rw [mu_N0_split]
  exact (ENNReal.add_sub_cancel_left hfinite).symm

/-- The support of Theorem 79 has exactly the stated mass `C`. -/
theorem mu_U7 : μ U7 = ENNReal.ofReal (C : ℝ) := by
  rw [mu_U7_from_loss, mu_N0_loss, mu_Omega, mu_N0, mu_N0_balanced, mu_N0_mixed,
    ← ENNReal.ofReal_ofNat 42, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_sub _ (by norm_num),
    ← ENNReal.ofReal_mul (p := (2 : ℝ)) (by norm_num),
    ← ENNReal.ofReal_sub _ (by norm_num)]
  congr 1
  norm_num [C]

private theorem mu_lowerCeilingLoss :
    μ (ceilingLoss ∩ {p | trace p < 3 / 2}) = ENNReal.ofReal (55 / 2048 : ℝ) := by
  rw [mu_lowerCeilingCells, lowerCeilingCells_integral]
  norm_num

theorem mu_ceilingLoss : μ ceilingLoss = ENNReal.ofReal (55 / 1024 : ℝ) := by
  rw [mu_ceilingLoss_split, mu_lowerCeilingLoss, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (p := (2 : ℝ)) (by norm_num)]
  congr 1
  norm_num

theorem mu_ceilingLoss_balanced :
    μ (ceilingLoss ∩ balanced) = ENNReal.ofReal (134173355669 / 2941777950300000000 : ℝ) := by
  rw [mu_ceilingBalancedCells, ceilingBalancedCells_integral]
  norm_num

theorem mu_ceilingLoss_mixed :
    μ ((ceilingLoss ∩ FPlus) \ balanced) =
      ENNReal.ofReal (196813181035147418047099 / 949275554159332482383700000000 : ℝ) := by
  rw [mu_ceilingMixedCells, ceilingMixedCells_integral]
  norm_num

/-- The increase in the support ceiling from the mixed regions in the two orientations. -/
theorem ceiling_mixed_gain : 2 * μ ((ceilingLoss ∩ FPlus) \ balanced) =
    ENNReal.ofReal (196813181035147418047099 / 474637777079666241191850000000 : ℝ) := by
  rw [mu_ceilingLoss_mixed, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (p := (2 : ℝ)) (by norm_num)]
  congr 1
  norm_num

/-- The ceiling union has the exact mass in Proposition 3. -/
theorem mu_ceiling : μ ceiling = ENNReal.ofReal (ceilingMass : ℝ) := by
  rw [mu_ceiling_reduction, mu_Omega, mu_ceilingLoss, mu_ceilingLoss_balanced, ceiling_mixed_gain,
    ← ENNReal.ofReal_ofNat 42, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (p := (2 : ℝ)) (by norm_num),
    ← ENNReal.ofReal_sub _ (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1
  norm_num [ceilingMass]

end ZetaSixth

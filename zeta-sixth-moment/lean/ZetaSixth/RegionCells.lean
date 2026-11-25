import ZetaSixth.CellPartitions
import ZetaSixth.RegionComplements
import Mathlib.Tactic.SplitIfs

/-!
# Cell partitions in short-sum coordinates

Here `k = x + y`. The endpoints are rational affine functions, and the partition
lemmas omit only the finitely many affine planes on which a face changes.
-/

namespace ZetaSixth.RegionCells

open Filter MeasureTheory Set

private def start : Affine1 := ⟨-1 / 4, 1 / 2⟩
private def turn : Affine1 := ⟨-1, 2⟩
private def half : Affine1 := ⟨0, 1 / 2⟩
private def quarter : Affine1 := ⟨1 / 4, 0⟩
private def spreadTraceCut : Affine1 := ⟨1, -1⟩
private def upperTraceStart : Affine1 := ⟨-3 / 2, 2⟩
private def balancedStart : Affine1 := ⟨-18 / 7, 5⟩
private def balancedSpreadCut : Affine1 := ⟨29 / 14, -4⟩
private def cap0 : Affine1 := ⟨21 / 2, -39 / 2⟩
private def cap1 : Affine1 := ⟨7 / 4, -3⟩
private def cap2 : Affine1 := ⟨1 / 2, -3 / 4⟩
private def cap3 : Affine1 := ⟨3 / 2, -5 / 2⟩

private def yFace : Affine2 := ⟨0, 1, -1⟩
private def lowerTraceFace : Affine2 := ⟨1, -1, 0⟩
private def upperTraceFace : Affine2 := ⟨3 / 2, -1, 0⟩
private def spreadFace : Affine2 := ⟨1 / 2, 0, 1⟩
private def balancedFace : Affine2 := ⟨18 / 7, -4, 0⟩
private def shortSumFace : Affine2 := ⟨0, 1, 0⟩

/-- The smaller coordinate bounds for the five cells of `N0` come from the
change of the larger-coordinate face at `k = 2/3` and `k = 5/6`. -/
def markedCells : List Cell :=
  [⟨1 / 2, 2 / 3, start, turn, yFace, spreadFace⟩,
   ⟨1 / 2, 2 / 3, turn, half, lowerTraceFace, spreadFace⟩,
   ⟨2 / 3, 5 / 6, start, spreadTraceCut, yFace, spreadFace⟩,
   ⟨2 / 3, 5 / 6, spreadTraceCut, half, yFace, upperTraceFace⟩,
   ⟨5 / 6, 1, upperTraceStart, half, yFace, upperTraceFace⟩]

/-- Cells of the intersection of `N0` with the balanced region. -/
def markedBalancedCells : List Cell :=
  [⟨1 / 2, 43 / 84, start, turn, yFace, spreadFace⟩,
   ⟨1 / 2, 43 / 84, turn, balancedSpreadCut, lowerTraceFace, spreadFace⟩,
   ⟨1 / 2, 43 / 84, balancedSpreadCut, half, lowerTraceFace, balancedFace⟩,
   ⟨43 / 84, 65 / 126, start, balancedSpreadCut, yFace, spreadFace⟩,
   ⟨43 / 84, 65 / 126, balancedSpreadCut, turn, yFace, balancedFace⟩,
   ⟨43 / 84, 65 / 126, turn, half, lowerTraceFace, balancedFace⟩,
   ⟨65 / 126, 11 / 21, balancedStart, turn, yFace, balancedFace⟩,
   ⟨65 / 126, 11 / 21, turn, half, lowerTraceFace, balancedFace⟩]

/-- The part of the mixed-row gain below `k = 10/19`, with every mark admitted. -/
def allMarkCells : List Cell :=
  [⟨1 / 2, 65 / 126, balancedSpreadCut, half, balancedFace, spreadFace⟩,
   ⟨65 / 126, 11 / 21, start, balancedStart, yFace, spreadFace⟩,
   ⟨65 / 126, 11 / 21, balancedStart, half, balancedFace, spreadFace⟩,
   ⟨11 / 21, 10 / 19, start, turn, yFace, spreadFace⟩,
   ⟨11 / 21, 10 / 19, turn, half, lowerTraceFace, spreadFace⟩]

/-- The two cells below the `a₀` cap above `k = 10/19`. -/
def twoMarkCells : List Cell :=
  [⟨10 / 19, 8 / 15, start, turn, yFace, spreadFace⟩,
   ⟨10 / 19, 8 / 15, turn, cap0, lowerTraceFace, spreadFace⟩]

/-- The seven cells in Table 1, in the printed order. -/
def sevenCells : List Cell :=
  [⟨35 / 66, 8 / 15, cap0, cap1, lowerTraceFace, spreadFace⟩,
   ⟨8 / 15, 7 / 13, start, turn, yFace, spreadFace⟩,
   ⟨8 / 15, 7 / 13, turn, cap1, lowerTraceFace, spreadFace⟩,
   ⟨7 / 13, 6 / 11, start, turn, yFace, spreadFace⟩,
   ⟨7 / 13, 6 / 11, turn, cap2, lowerTraceFace, spreadFace⟩,
   ⟨6 / 11, 4 / 7, start, cap2, yFace, spreadFace⟩,
   ⟨4 / 7, 7 / 12, start, cap3, yFace, spreadFace⟩]

def mixedCells : List Cell := allMarkCells ++ twoMarkCells ++ sevenCells

/-- The lower-trace half of the ceiling complement, letting reflection give the other half. -/
def lowerCeilingCells : List Cell :=
  [⟨1 / 2, 5 / 8, quarter, half, lowerTraceFace, shortSumFace⟩,
   ⟨5 / 8, 2 / 3, quarter, turn, yFace, shortSumFace⟩,
   ⟨5 / 8, 2 / 3, turn, half, lowerTraceFace, shortSumFace⟩,
   ⟨2 / 3, 3 / 4, quarter, half, yFace, shortSumFace⟩,
   ⟨3 / 4, 7 / 8, quarter, half, yFace, upperTraceFace⟩,
   ⟨7 / 8, 1, upperTraceStart, half, yFace, upperTraceFace⟩]

/-- The ceiling complement intersected with the balanced region. -/
def ceilingBalancedCells : List Cell :=
  [⟨1 / 2, 18 / 35, quarter, half, lowerTraceFace, shortSumFace⟩,
   ⟨18 / 35, 11 / 21, quarter, half, lowerTraceFace, balancedFace⟩]

/-- The additional part of the ceiling complement removed by the mixed row. -/
def ceilingMixedCells : List Cell :=
  [⟨18 / 35, 11 / 21, quarter, half, balancedFace, shortSumFace⟩,
   ⟨11 / 21, 10 / 19, quarter, half, lowerTraceFace, shortSumFace⟩]

open Lean.Parser.Tactic in
local macro "norm_cell_faces" loc:(location)? : tactic =>
  `(tactic| norm_num [Cell.union, Cell.set, Cell.kBand, Cell.xBand, Cell.zBand,
      Affine1.eval, Affine2.eval, start, turn, half, quarter, spreadTraceCut, upperTraceStart,
      balancedStart, balancedSpreadCut, cap0, cap1, cap2, cap3, yFace, lowerTraceFace,
      upperTraceFace, spreadFace, balancedFace, shortSumFace] $(loc)?)

local macro "check_cell_orders" : tactic =>
  `(tactic|
    (simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
     repeat' first
       | (apply Cell.ordered_of_corners <;> norm_cell_faces) <;> done
       | exact List.forall_mem_nil _
       | constructor))

local macro "check_cell_separation" : tactic =>
  `(tactic|
    (simp [List.pairwise_cons, List.forall_mem_cons]
     repeat' apply And.intro
     all_goals
       first
         | apply Cell.disjoint_of_kHi_le_kLo
           norm_num
           done
         | rw [Set.disjoint_left]
           rintro ⟨k, x, z⟩ hp hq
           norm_cell_faces at hp hq
           rcases hp with ⟨⟨hkl, hku⟩, ⟨hxl, hxu⟩, _, _⟩
           rcases hq with ⟨⟨hkl', hku'⟩, ⟨hxl', hxu'⟩, _, _⟩
           linarith only [hkl, hku, hxl, hxu, hkl', hku', hxl', hxu']))

private theorem marked_ordered : ∀ c ∈ markedCells, c.Ordered := by
  unfold markedCells
  check_cell_orders

private theorem marked_disjoint : markedCells.Pairwise fun c d => Disjoint c.set d.set := by
  unfold markedCells
  check_cell_separation

private theorem markedBalanced_ordered : ∀ c ∈ markedBalancedCells, c.Ordered := by
  unfold markedBalancedCells
  check_cell_orders

set_option maxHeartbeats 1000000 in
private theorem markedBalanced_disjoint :
    markedBalancedCells.Pairwise fun c d => Disjoint c.set d.set := by
  unfold markedBalancedCells
  check_cell_separation

private theorem mixed_ordered : ∀ c ∈ mixedCells, c.Ordered := by
  simp only [mixedCells, allMarkCells, twoMarkCells, sevenCells, List.cons_append, List.nil_append]
  check_cell_orders

set_option maxHeartbeats 2500000 in
private theorem mixed_disjoint : mixedCells.Pairwise fun c d => Disjoint c.set d.set := by
  simp only [mixedCells, allMarkCells, twoMarkCells, sevenCells, List.cons_append, List.nil_append]
  check_cell_separation

private theorem lowerCeiling_ordered : ∀ c ∈ lowerCeilingCells, c.Ordered := by
  unfold lowerCeilingCells
  check_cell_orders

private theorem lowerCeiling_disjoint :
    lowerCeilingCells.Pairwise fun c d => Disjoint c.set d.set := by
  unfold lowerCeilingCells
  check_cell_separation

private theorem ceilingBalanced_ordered : ∀ c ∈ ceilingBalancedCells, c.Ordered := by
  unfold ceilingBalancedCells
  check_cell_orders

private theorem ceilingBalanced_disjoint :
    ceilingBalancedCells.Pairwise fun c d => Disjoint c.set d.set := by
  unfold ceilingBalancedCells
  check_cell_separation

private theorem ceilingMixed_ordered : ∀ c ∈ ceilingMixedCells, c.Ordered := by
  unfold ceilingMixedCells
  check_cell_orders

private theorem ceilingMixed_disjoint :
    ceilingMixedCells.Pairwise fun c d => Disjoint c.set d.set := by
  unfold ceilingMixedCells
  check_cell_separation

private theorem marked_ae :
    (shortCoordinates.symm ⁻¹' N0 : Set Point) =ᵐ[volume] Cell.union markedCells := by
  filter_upwards [ae_short_coordinate_ne (2 / 3), ae_short_coordinate_ne (5 / 6),
    ae_second_coordinate_ne (-1) 2, ae_second_coordinate_ne 1 (-1)] with p hk1 hk2 hx1 hx2
  rcases p with ⟨k, x, z⟩
  apply propext
  change shortCoordinates.symm (k, x, z) ∈ N0 ↔ (k, x, z) ∈ Cell.union markedCells
  simp only [shortCoordinates_symm_apply, N0, Ω, trace, shortSum,
    Set.mem_inter_iff, Set.mem_setOf_eq, markedCells]
  norm_cell_faces
  grind (splits := 100)

private theorem markedBalanced_ae :
    (shortCoordinates.symm ⁻¹' (N0 ∩ balanced) : Set Point) =ᵐ[volume]
      Cell.union markedBalancedCells := by
  filter_upwards [ae_short_coordinate_ne (43 / 84), ae_short_coordinate_ne (65 / 126),
    ae_second_coordinate_ne (-1) 2, ae_second_coordinate_ne (29 / 14) (-4)] with p hk1 hk2 hx1 hx2
  rcases p with ⟨k, x, z⟩
  apply propext
  change shortCoordinates.symm (k, x, z) ∈ N0 ∩ balanced ↔
    (k, x, z) ∈ Cell.union markedBalancedCells
  simp only [shortCoordinates_symm_apply, N0, Ω, balanced, trace, shortSum,
    Set.mem_inter_iff, Set.mem_setOf_eq, markedBalancedCells]
  norm_cell_faces
  grind (splits := 100)

set_option maxHeartbeats 0 in
private theorem mixed_ae :
    (shortCoordinates.symm ⁻¹' ((N0 ∩ FPlus) \ balanced) : Set Point) =ᵐ[volume]
      Cell.union mixedCells := by
  filter_upwards [ae_short_coordinate_ne (65 / 126), ae_short_coordinate_ne (11 / 21),
    ae_short_coordinate_ne (10 / 19), ae_short_coordinate_ne (8 / 15),
    ae_short_coordinate_ne (7 / 13),
    ae_short_coordinate_ne (6 / 11), ae_short_coordinate_ne (4 / 7),
    ae_second_coordinate_ne (-1) 2, ae_second_coordinate_ne (-18 / 7) 5,
    ae_second_coordinate_ne (21 / 2) (-39 / 2),
    ae_third_coordinate_ne (18 / 7) (-4) 0] with p hk1 hk2 hk3 hk4 hk5 hk6 hk7 hx1 hx2 hx3 hz
  rcases p with ⟨k, x, z⟩
  apply propext
  change shortCoordinates.symm (k, x, z) ∈ (N0 ∩ FPlus) \ balanced ↔
    (k, x, z) ∈ Cell.union mixedCells
  simp only [shortCoordinates_symm_apply, N0, Ω, balanced, FPlus, PPlus,
    trace, shortSum, Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq,
    mixedCells, allMarkCells, twoMarkCells, sevenCells, List.cons_append, List.nil_append]
  have hsum : x + (k - x) = k := by ring
  rw [hsum]
  simp only [xPlus]
  norm_cell_faces
  split_ifs <;> (try simp only [lt_max_iff]) <;> grind (splits := 100)

private theorem lowerCeiling_ae :
    (shortCoordinates.symm ⁻¹' (ceilingLoss ∩ {p | trace p < 3 / 2}) : Set Point)
      =ᵐ[volume] Cell.union lowerCeilingCells := by
  filter_upwards [ae_short_coordinate_ne (5 / 8), ae_short_coordinate_ne (2 / 3),
    ae_short_coordinate_ne (3 / 4), ae_short_coordinate_ne (7 / 8),
    ae_second_coordinate_ne (-1) 2] with p hk1 hk2 hk3 hk4 hx
  rcases p with ⟨k, x, z⟩
  apply propext
  change shortCoordinates.symm (k, x, z) ∈ ceilingLoss ∩ {p | trace p < 3 / 2} ↔
    (k, x, z) ∈ Cell.union lowerCeilingCells
  simp only [shortCoordinates_symm_apply, ceilingLoss, Ω, trace, shortSum,
    Set.mem_inter_iff, Set.mem_setOf_eq, lowerCeilingCells]
  norm_cell_faces
  grind (splits := 100)

private theorem ceilingBalanced_ae :
    (shortCoordinates.symm ⁻¹' (ceilingLoss ∩ balanced) : Set Point) =ᵐ[volume]
      Cell.union ceilingBalancedCells := by
  filter_upwards [ae_short_coordinate_ne (18 / 35)] with p hk
  rcases p with ⟨k, x, z⟩
  apply propext
  change shortCoordinates.symm (k, x, z) ∈ ceilingLoss ∩ balanced ↔
    (k, x, z) ∈ Cell.union ceilingBalancedCells
  simp only [shortCoordinates_symm_apply, ceilingLoss, balanced, Ω, trace,
    shortSum, Set.mem_inter_iff, Set.mem_setOf_eq, ceilingBalancedCells]
  norm_cell_faces
  grind (splits := 100)

private theorem ceilingMixed_ae :
    (shortCoordinates.symm ⁻¹' ((ceilingLoss ∩ FPlus) \ balanced) : Set Point) =ᵐ[volume]
      Cell.union ceilingMixedCells := by
  filter_upwards [ae_short_coordinate_ne (11 / 21),
    ae_third_coordinate_ne (18 / 7) (-4) 0] with p hk hz
  rcases p with ⟨k, x, z⟩
  apply propext
  change shortCoordinates.symm (k, x, z) ∈ (ceilingLoss ∩ FPlus) \ balanced ↔
    (k, x, z) ∈ Cell.union ceilingMixedCells
  simp only [shortCoordinates_symm_apply, ceilingLoss, Ω, balanced, FPlus, PPlus,
    trace, shortSum, Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq,
    ceilingMixedCells]
  have hsum : x + (k - x) = k := by ring
  rw [hsum]
  simp only [xPlus]
  norm_cell_faces
  split_ifs <;> (try simp only [lt_max_iff]) <;> grind (splits := 100)

private theorem original_mem_Ω {p : Point} (hp : (shortCoordinates p).2.1 ∈ Set.Ioo 0 ((shortCoordinates p).1 / 2))
    (hyz : (shortCoordinates p).1 - (shortCoordinates p).2.1 < (shortCoordinates p).2.2)
    (hz : (shortCoordinates p).2.2 < 1) : p ∈ Ω := by
  simp only [shortCoordinates_apply, Set.mem_Ioo] at hp hyz hz
  exact ⟨hp.1, by linarith [hp.2], by linarith, hz⟩

local macro "check_cell_containment" : tactic =>
  `(tactic|
    (intro p hp
     refine original_mem_Ω ?_ ?_ ?_ <;>
       (simp at hp ⊢
        norm_cell_faces at hp
        grind (splits := 100))))

theorem mu_markedCells : μ N0 = ENNReal.ofReal (Cell.massSum markedCells : ℝ) := by
  apply mu_from_cell_partition markedCells marked_ae marked_ordered _ marked_disjoint
  unfold markedCells
  check_cell_containment

theorem mu_markedBalancedCells :
    μ (N0 ∩ balanced) = ENNReal.ofReal (Cell.massSum markedBalancedCells : ℝ) := by
  apply mu_from_cell_partition markedBalancedCells markedBalanced_ae markedBalanced_ordered _
    markedBalanced_disjoint
  unfold markedBalancedCells
  check_cell_containment

theorem mu_mixedCells :
    μ ((N0 ∩ FPlus) \ balanced) = ENNReal.ofReal (Cell.massSum mixedCells : ℝ) := by
  apply mu_from_cell_partition mixedCells mixed_ae mixed_ordered _ mixed_disjoint
  simp only [mixedCells, allMarkCells, twoMarkCells, sevenCells, List.cons_append, List.nil_append]
  check_cell_containment

theorem mu_lowerCeilingCells :
    μ (ceilingLoss ∩ {p | trace p < 3 / 2}) =
      ENNReal.ofReal (Cell.massSum lowerCeilingCells : ℝ) := by
  apply mu_from_cell_partition lowerCeilingCells lowerCeiling_ae lowerCeiling_ordered _
    lowerCeiling_disjoint
  unfold lowerCeilingCells
  check_cell_containment

theorem mu_ceilingBalancedCells :
    μ (ceilingLoss ∩ balanced) = ENNReal.ofReal (Cell.massSum ceilingBalancedCells : ℝ) := by
  apply mu_from_cell_partition ceilingBalancedCells ceilingBalanced_ae ceilingBalanced_ordered _
    ceilingBalanced_disjoint
  unfold ceilingBalancedCells
  check_cell_containment

theorem mu_ceilingMixedCells :
    μ ((ceilingLoss ∩ FPlus) \ balanced) =
      ENNReal.ofReal (Cell.massSum ceilingMixedCells : ℝ) := by
  apply mu_from_cell_partition ceilingMixedCells ceilingMixed_ae ceilingMixed_ordered _
    ceilingMixed_disjoint
  unfold ceilingMixedCells
  check_cell_containment

end ZetaSixth.RegionCells

import HadwigerNelson.Packing.PairCounts
import HadwigerNelson.Packing.LocalCounts

namespace HadwigerNelson.Packing
open Finset
noncomputable section

/-- Count short pairs inside the removed sets and between them and the two separated sets. -/
theorem close_pairs_bound (X R D : Finset Plane) (hR : R ⊆ X) (hD : D ⊆ R)
    (sepR : separated R (53/10000)) (sepD : separated D (1837/250000)) :
    let s := X.card - R.card
    let j := R.card - D.card
    shortPairs X (53/10000) ≤ 5*s + s.choose 2 ∧
      shortPairs X (1837/250000) ≤ 14*s + 8*j + s.choose 2 := by
  classical
  let U := X \ R
  let V := R \ D
  have s : U.card = X.card-R.card := Finset.card_sdiff_of_subset hR
  have j : V.card = R.card-D.card := Finset.card_sdiff_of_subset hD
  let small : ℝ := 53/10000
  let large : ℝ := 1837/250000
  have within {B : Finset Plane} {x y d} (h : y ∈ closeNeighbours B x d) :
      y ∈ B ∧ x ≠ y ∧ dist y x < d := by
    simpa only [dist_comm x y] using Finset.mem_filter.mp h
  have separatedSubset (x : Plane) (d : ℝ) : separated (closeNeighbours R x d) small :=
    fun _ hy _ hz ne ↦ sepR _ (within hy).1 _ (within hz).1 ne
  have five : between U R small ≤ U.card*5 := between_bound U R small 5 (by
    intro x _
    exact five_neighbours _ x (by norm_num [small]) (separatedSubset x small)
      (fun _ hy ↦ (within hy).2.2.le))
  have fourteen : between U R large ≤ U.card*14 := between_bound U R large 14 (by
    intro x _
    exact fourteen_neighbours _ x (separatedSubset x large) (fun _ hy ↦ (within hy).2.2.le))
  have eight : between V R large ≤ V.card*8 := between_bound V R large 8 (by
    intro x hx
    exact eight_neighbours _ x (separatedSubset x large) (by
      intro y hy
      obtain ⟨yr,ne,h⟩ := within hy
      exact ⟨(sepR y yr x (Finset.mem_sdiff.mp hx).1 ne.symm).le,h.le⟩))
  have split : between V R large = between V V large + between V D large := by
    conv_lhs => arg 2; rw [← Finset.sdiff_union_of_subset hD]
    exact between_add V D V large Finset.sdiff_disjoint
  have rbound : between R R large ≤ 2*(V.card*8) := by
    have decomp := between_partition R D large hD
    change between R R large = between V V large + 2*between V D large + between D D large at decomp
    rw [between_self_zero D sepD] at decomp
    omega
  change between X X small / 2 ≤ _ ∧ between X X large / 2 ≤ _
  rw [←s,←j]
  constructor
  · have a := between_partition X R small hR
    change between X X small = between U U small + 2*between U R small + between R R small at a
    rw [between_self_zero R sepR] at a
    have b := between_self_bound U small
    omega
  · have a := between_partition X R large hR
    change between X X large = between U U large + 2*between U R large + between R R large at a
    have b := between_self_bound U large
    omega

end
end HadwigerNelson.Packing

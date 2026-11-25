import HadwigerNelson.Centres.AdjacentMarks
import HadwigerNelson.Centres.BudgetDefs
import HadwigerNelson.Packing.PairCounts

namespace HadwigerNelson.Centres
open Finset Crossings
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Ordered endpoints, with one unit of weight per circle carrying their short arc. -/
def circleCarriers (X : Finset Plane) (r : ℝ) (p q : Plane) : Finset Plane :=
  X.filter fun c ↦ consecutive X c p q ∧ dist p q < r

theorem circleCarriers_comm (X : Finset Plane) (r : ℝ) (p q : Plane) :
    circleCarriers X r p q = circleCarriers X r q p := by
  ext c; simp only [circleCarriers,mem_filter,consecutive_comm (c:=c) (p:=p) (q:=q),dist_comm p q]

theorem circleCarriers_le_two (X : Finset Plane) (r : ℝ) (p q : Plane) :
    (circleCarriers X r p q).card ≤ 2 := by
  by_cases same : p=q
  · subst q; simp [circleCarriers,consecutive]
  obtain ⟨T,size,spec⟩ := unit_intersections_le_two p q same
  apply (Finset.card_le_card (t:=T) ?_).trans size
  intro c hc
  have yes := (Finset.mem_filter.mp hc).2.1
  exact (spec _).mpr ⟨yes.2.1,yes.2.2.1⟩

/-- Sum of the ordered arc multiplicities on a rectangle of endpoint pairs. -/
def arcCount (X : Finset Plane) (r : ℝ) (A B : Finset Plane) : ℕ :=
  ∑ p ∈ A, ∑ q ∈ B, (circleCarriers X r p q).card

theorem arcCount_comm (X A B : Finset Plane) (r : ℝ) : arcCount X r A B = arcCount X r B A := by
  unfold arcCount
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun p _ ↦ congrArg Finset.card (circleCarriers_comm ..)

theorem arcCount_union (X A B C : Finset Plane) (r : ℝ) (d : Disjoint A B) :
    arcCount X r (A∪B) C = arcCount X r A C + arcCount X r B C := Finset.sum_union d

theorem arcCount_partition (X A : Finset Plane) (r : ℝ) (hA : A ⊆ X) (sep : Packing.separated A r) :
    arcCount X r X X = arcCount X r (X\A) (X\A) + 2*arcCount X r (X\A) A ∧
    arcCount X r (X\A) X = arcCount X r (X\A) (X\A) + arcCount X r (X\A) A := by
  have zero : arcCount X r A A = 0 := by
    apply Finset.sum_eq_zero; intro p hp; apply Finset.sum_eq_zero; intro q hq
    apply Finset.card_eq_zero.mpr; apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc; obtain ⟨_,yes,near⟩ := Finset.mem_filter.mp hc
    exact (sep p hp q hq yes.1).not_gt near
  have split (B) : arcCount X r X B = arcCount X r (X\A) B + arcCount X r A B := by
    conv_lhs => arg 3; rw [← Finset.sdiff_union_of_subset hA]
    exact arcCount_union X _ _ B r Finset.sdiff_disjoint
  have part (B) : arcCount X r B X = arcCount X r B (X\A) + arcCount X r B A := by
    rw [arcCount_comm X B X,split,arcCount_comm X _ B,arcCount_comm X A B]
  constructor
  · rw [split X,part,part A,zero,arcCount_comm X A (X\A)]; omega
  · exact part _

theorem arcCount_pairs (X A B : Finset Plane) (r : ℝ) :
    arcCount X r A B ≤ 2*Packing.between A B r := by
  unfold arcCount Packing.between Packing.closeNeighbours
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro p _
  rw [Finset.card_filter,Finset.mul_sum]
  apply Finset.sum_le_sum; intro q _
  split
  · simpa using circleCarriers_le_two X r p q
  next no =>
    simp only [mul_zero,Nat.le_zero,Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr; intro c hc
    have yes := (Finset.mem_filter.mp hc).2
    exact no ⟨yes.1.1,yes.2⟩

theorem arcCount_endpoint (X U : Finset Plane) (r : ℝ) (hU : U ⊆ X) :
    arcCount X r U X ≤ 2*∑ p ∈ U, unitDegree X p := by
  unfold arcCount; rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro p hp
  change (∑ q ∈ X, (X.filter fun c ↦ consecutive X c p q ∧ dist p q < r).card) ≤ _
  rw [sum_filter_card]
  unfold unitDegree; rw [Finset.card_filter,Finset.mul_sum]
  apply Finset.sum_le_sum; intro c _
  split
  · have sub : (X.filter fun q ↦ consecutive X c p q ∧ dist p q < r) ⊆ X.filter (consecutive X c p) :=
      fun q h ↦ Finset.mem_filter.mpr ⟨(mem_filter.mp h).1,(mem_filter.mp h).2.1⟩
    simpa using (Finset.card_le_card sub).trans (CircleMarks.adjacent_count X c p (hU hp))
  next no =>
    simp only [mul_zero,Nat.le_zero,Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr; intro q h
    exact no (by rw [dist_comm]; exact (mem_filter.mp h).2.1.2.1)

theorem shortArcCount_eq (X : Finset Plane) (r : ℝ) : shortArcCount X r = arcCount X r X X / 2 := by
  unfold shortArcCount arcCount circleCarriers
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro p _
  exact sum_filter_card X X _

theorem twice_shortDoubled_le (X : Finset Plane) (r : ℝ) :
    2*shortDoubledCount X r ≤ shortArcCount X r := by
  let double := fun p q ↦ dist p q < r ∧ ∃ u ∈ X, ∃ v ∈ X, u ≠ v ∧ consecutive X u p q ∧ consecutive X v p q
  let N := ∑ p ∈ X, (X.filter (double p)).card
  have bound : 2*N ≤ arcCount X r X X := by
    dsimp [N,arcCount]; rw [Finset.mul_sum]; apply Finset.sum_le_sum
    intro p _; rw [Finset.card_filter,Finset.mul_sum]; apply Finset.sum_le_sum; intro q _
    split
    next h =>
      obtain ⟨near,u,hu,v,hv,ne,yes,other⟩ := h
      have sub : ({u,v} : Finset Plane) ⊆ circleCarriers X r p q := by
        intro c hc; rcases Finset.mem_insert.mp hc with rfl|only
        · exact mem_filter.mpr ⟨hu,yes,near⟩
        · have eq := Finset.mem_singleton.mp only; subst c; exact mem_filter.mpr ⟨hv,other,near⟩
      simpa [ne] using Finset.card_le_card sub
    next => simp
  change 2*(N/2) ≤ _
  rw [shortArcCount_eq]
  omega

end
end HadwigerNelson.Centres

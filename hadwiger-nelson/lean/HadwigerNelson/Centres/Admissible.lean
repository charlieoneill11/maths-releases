import HadwigerNelson.Centres.ArcCounts
import HadwigerNelson.Packing.LocalCounts

namespace HadwigerNelson.Centres
open Finset Crossings Packing
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem even_pair_count (X : Finset Plane) (r : ℝ) :
    Packing.between X X r = 2*shortPairs X r := by
  let f (p q : Plane) : ℕ := if p ≠ q ∧ dist p q < r then 1 else 0
  have symm (p q : Plane) : f p q = f q p := by simp only [f,ne_comm (a:=p) (b:=q),dist_comm p q]
  have even : Even (∑ p ∈ X, ∑ q ∈ X, f p q) := by
    induction X using Finset.induction_on with
    | empty => simp
    | @insert p X hp ih =>
      obtain ⟨k,hk⟩ := ih
      refine ⟨k+∑ q ∈ X, f p q,?_⟩
      rw [Finset.sum_insert hp]
      simp_rw [Finset.sum_insert hp,Finset.sum_add_distrib]
      rw [hk,show f p p=0 by simp [f]]
      rw [Finset.sum_congr (s₁:=X) rfl fun q _ ↦ symm q p]
      simp only [Nat.zero_add]
      ac_rfl
  obtain ⟨k,hk⟩ := even
  have eq : Packing.between X X r = ∑ p ∈ X, ∑ q ∈ X, f p q := by
    simp only [Packing.between,closeNeighbours,Finset.card_filter,f]
  change Packing.between X X r = 2*(Packing.between X X r/2)
  omega

/-- Bounds at a single separation radius for any set of representatives. -/
theorem admissible_at (X P : Finset Plane) (r : ℝ) (hr : 0 < r)
    (hP : P ⊆ X) (sep : separated P r) (pairs : ℕ) (hpairs : shortPairs X r ≤ pairs) :
    let h := X.card-P.card
    let L : ℝ := outsideDegree X P
    admissible X r (min L (min (pairs:ℝ) ((L+5*h)/2))) := by
  let U := X\P
  have size : U.card = X.card-P.card := Finset.card_sdiff_of_subset hP
  have mixed : Packing.between U P r ≤ U.card*5 := between_bound U P r 5 (by
    intro p _
    apply five_neighbours _ p hr
    · exact fun x hx y hy ne ↦ sep x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 ne
    · intro q h; rw [dist_comm]; exact (mem_filter.mp h).2.2.le)
  let arcs := shortArcCount X r
  let doubles := shortDoubledCount X r
  let L := outsideDegree X P
  have ds : 2*doubles ≤ arcs := twice_shortDoubled_le X r
  have parts := arcCount_partition X P r hP sep
  change arcCount X r X X = arcCount X r U U + 2*arcCount X r U P ∧
    arcCount X r U X = arcCount X r U U + arcCount X r U P at parts
  have touch : arcCount X r U X ≤ 2*L := arcCount_endpoint X U r Finset.sdiff_subset
  have cross := arcCount_pairs X U P r
  have total := arcCount_pairs X X X r
  rw [even_pair_count] at total
  have half : arcs = arcCount X r X X /2 := shortArcCount_eq X r
  have arL : arcs ≤ 2*L := by omega
  have arP : arcs ≤ 2*pairs := by omega
  have arM : arcs ≤ L+5*U.card := by omega
  have arL' : (arcs:ℝ) ≤ 2*L := by exact_mod_cast arL
  have arP' : (arcs:ℝ) ≤ 2*pairs := by exact_mod_cast arP
  have arM' : (arcs:ℝ) ≤ L+5*U.card := by exact_mod_cast arM
  have ds' : 2*(doubles:ℝ) ≤ arcs := by exact_mod_cast ds
  change 0 ≤ min (L:ℝ) (min (pairs:ℝ) (((L:ℝ)+5*(X.card-P.card:ℕ))/2)) ∧
    (doubles:ℝ) ≤ _ ∧ (arcs:ℝ) ≤ _
  rw [←size]
  refine ⟨le_min (by positivity) (le_min (by positivity) (by positivity)), ?_, ?_⟩
  · exact le_min (by linarith) (le_min (by linarith) (by linarith))
  · rw [mul_min_of_nonneg _ _ (by norm_num : 0≤(2:ℝ)),mul_min_of_nonneg _ _ (by norm_num : 0≤(2:ℝ))]
    exact le_min arL' (le_min arP' (by linarith))

theorem physical_admissible_budgets (X R D : Finset Plane) (hR : Forest.maximalSeparated X R δR)
    (hD : Forest.maximalSeparated R D δ) :
    let s := X.card-R.card
    let j := R.card-D.card
    let LR : ℝ := outsideDegree X R
    let LD : ℝ := outsideDegree X D
    admissible X δR (min LR (min (5*s+s.choose 2 : ℕ) ((LR+5*s)/2))) ∧
    admissible X δ (min LD (min (14*s+8*j+s.choose 2 : ℕ) ((LD+5*(s+j))/2))) := by
  have pairs := Packing.close_pairs X R D hR.1 hD.1 hR.2.1 hD.2.1
  have sR := Finset.card_le_card hR.1
  have sD := Finset.card_le_card hD.1
  have h : X.card-D.card = (X.card-R.card) + (R.card-D.card) := by omega
  refine ⟨admissible_at X R δR (by norm_num [δR]) hR.1 hR.2.1 _ pairs.1,?_⟩
  simpa only [h,Nat.cast_add] using admissible_at X D δ (by norm_num [δ]) (hD.1.trans hR.1) hD.2.1 _ pairs.2

end
end HadwigerNelson.Centres

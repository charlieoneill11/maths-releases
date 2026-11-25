import Chowla.Model.Partitions
import Chowla.Model.OneException

namespace Chowla

open scoped BigOperators

/-- Expand a partition sum by the unique block containing a marked label. -/
theorem partitionWeight_marked {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (w : Finset ι → R) {U : Finset ι} {a : ι} (ha : a ∈ U) :
    partitionWeight w U =
      ∑ B ∈ (U.powerset.filter fun B => a ∈ B), w B * partitionWeight w (U \ B) := by
  classical
  let S := U.powerset.filter fun B => a ∈ B
  have hterm (P : Finpartition U) :
      (∏ B ∈ P.parts, w B) =
        ∑ B ∈ S, (if B ∈ P.parts then w B * ∏ T ∈ P.parts.erase B, w T else 0) := by
    obtain ⟨B, hB, hu⟩ := P.existsUnique_mem ha
    have hbS : B ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (P.le hB.1), hB.2⟩
    rw [Finset.sum_eq_single B]
    · rw [if_pos hB.1, Finset.mul_prod_erase _ _ hB.1]
    · intro T hT hne
      have haT := (Finset.mem_filter.mp hT).2
      exact if_neg fun hp => hne (hu T ⟨hp, haT⟩)
    · exact fun h => (h hbS).elim
  change partitionWeight w U = ∑ B ∈ S, w B * partitionWeight w (U \ B)
  unfold partitionWeight at *
  simp_rw [hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun B hB => ?_
  have hb : B ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
  have hne : B ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨a, (Finset.mem_filter.mp hB).2⟩
  have hfactor (P : Finpartition U) :
      (if B ∈ P.parts then w B * ∏ T ∈ P.parts.erase B, w T else 0) =
        w B * (if B ∈ P.parts then ∏ T ∈ P.parts.erase B, w T else 0) := by
    rw [mul_ite, mul_zero]
  simp_rw [hfactor, ← Finset.mul_sum, sum_partitions_containing w hb hne]
  rfl

/-- A partition polynomial with a marked label admits at most one exceptional block
among the blocks that do not contain the mark. -/
theorem partitionWeight_add_exception {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (g d : Finset ι → R) (U : Finset ι)
    (hd : ∀ B C : Finset ι, B ⊆ U → C ⊆ U → B ≠ C → Disjoint B C → d B * d C = 0) :
    partitionWeight (fun B => g B + d B) U =
      partitionWeight g U +
        ∑ B ∈ U.powerset.erase ∅, d B * partitionWeight g (U \ B) := by
  classical
  have hexpand (P : Finpartition U) :
      (∏ B ∈ P.parts, (g B + d B)) = (∏ B ∈ P.parts, g B) +
        ∑ B ∈ P.parts, d B * ∏ T ∈ P.parts.erase B, g T :=
    prod_add_eq_at_most_one_exception P.parts g d (fun B hb C hc hne =>
      hd B C (P.le hb) (P.le hc) hne (P.disjoint hb hc hne))
  rw [partitionWeight, partitionWeight]
  simp_rw [hexpand, Finset.sum_add_distrib]
  congr 1
  let S := U.powerset.erase ∅
  have hsubset (P : Finpartition U) : P.parts ⊆ S :=
    fun B hb => Finset.mem_erase.mpr ⟨P.ne_bot hb, Finset.mem_powerset.mpr (P.le hb)⟩
  have hval (P : Finpartition U) :
      (∑ B ∈ P.parts, d B * ∏ T ∈ P.parts.erase B, g T) =
        ∑ B ∈ S, d B * (if B ∈ P.parts then ∏ T ∈ P.parts.erase B, g T else 0) := by
    simp_rw [mul_ite, mul_zero, ← Finset.sum_filter]
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hsubset P)]
  simp_rw [hval]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun B hb => ?_
  rw [← Finset.mul_sum, sum_partitions_containing]
  · exact Finset.mem_powerset.mp ((Finset.mem_erase.mp hb).2)
  · exact (Finset.mem_erase.mp hb).1

end Chowla

import Chowla.Model.Moments
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Chowla

open Finset
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

private theorem block_sdiff_self {U B T : Finset ι} (P : Finpartition U)
    (hB : B ∈ P.parts) (hT : T ∈ P.parts) (hne : T ≠ B) :
    ¬T ⊆ B ∧ T \ B = T := by
  have hd : Disjoint T B := P.disjoint hT hB hne
  exact ⟨fun h => P.ne_bot hT (hd.eq_bot_of_le h), sdiff_eq_self_of_disjoint hd⟩

theorem Finpartition.avoid_parts_eq_erase {U B : Finset ι} (P : Finpartition U)
    (hB : B ∈ P.parts) : (P.avoid B).parts = P.parts.erase B := by
  ext T
  rw [Finpartition.mem_avoid, Finset.mem_erase]
  constructor
  · rintro ⟨S, hS, hnot, hST⟩
    have hne : S ≠ B := by
      intro he
      subst S
      exact hnot le_rfl
    have he : S = T := (block_sdiff_self P hB hS hne).2.symm.trans hST
    rw [← he]
    exact ⟨hne, hS⟩
  · rintro ⟨hne, hT⟩
    obtain ⟨hsub, he⟩ := block_sdiff_self P hB hT hne
    exact ⟨T, hT, hsub, he⟩

/-- A partition containing a specified nonempty block is determined by the partition
of the complement of that block. -/
def finpartitionWithBlock {U B : Finset ι} (hb : B ⊆ U) (hne : B ≠ ∅) :
    Finpartition (U \ B) ≃ {P : Finpartition U // B ∈ P.parts} where
  toFun P :=
    ⟨P.extend hne disjoint_sdiff_self_left (by simpa only [sup_eq_union] using sdiff_union_of_subset hb),
      mem_insert_self _ _⟩
  invFun P := P.val.avoid B
  left_inv P := by
    ext1
    rw [Finpartition.avoid_parts_eq_erase _ (mem_insert_self B P.parts), Finpartition.extend_parts]
    apply erase_insert
    intro hB
    have hd : Disjoint B (U \ B) := disjoint_sdiff_self_right
    have H : Disjoint B B := hd.mono_right (P.le hB)
    exact hne (disjoint_self.mp H)
  right_inv P := by
    apply Subtype.ext
    ext1
    rw [Finpartition.extend_parts, Finpartition.avoid_parts_eq_erase _ P.property,
      Finset.insert_erase P.property]

/-- The sum of products of block weights over all partitions of a finite set. -/
noncomputable def partitionWeight {R : Type*} [CommSemiring R] (w : Finset ι → R)
    (U : Finset ι) : R :=
  ∑ P : Finpartition U, ∏ B ∈ P.parts, w B

/-- Isolating one block of a partition leaves an unrestricted partition of its complement. -/
theorem sum_partitions_containing {R : Type*} [CommSemiring R]
    (w : Finset ι → R) {U B : Finset ι} (hb : B ⊆ U) (hne : B ≠ ∅) :
    (∑ P : Finpartition U, if B ∈ P.parts then ∏ T ∈ P.parts.erase B, w T else 0) =
      partitionWeight w (U \ B) := by
  classical
  let e := finpartitionWithBlock hb hne
  rw [partitionWeight, ← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun Q _ => (e Q).val) ?_ ?_ ?_ ?_
  · intro Q _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e Q).property⟩
  · intro Q _ Q' _ h
    exact e.injective (Subtype.ext h)
  · intro P hP
    let p : {P : Finpartition U // B ∈ P.parts} := ⟨P, (Finset.mem_filter.mp hP).2⟩
    exact ⟨e.symm p, Finset.mem_univ _, congrArg Subtype.val (e.apply_symm_apply p)⟩
  · intro Q _
    have hparts : ((e Q).val.avoid B).parts = Q.parts :=
      congrArg Finpartition.parts (e.symm_apply_apply Q)
    rw [Finpartition.avoid_parts_eq_erase _ (e Q).property] at hparts
    rw [hparts]

/-- Changing the weight of one block by `a` changes the partition sum by `a` times
the partition sum of the complementary set. -/
theorem partitionWeight_update {R : Type*} [CommSemiring R]
    (w : Finset ι → R) {U B : Finset ι} (a : R) (hb : B ⊆ U) (hne : B ≠ ∅) :
    partitionWeight (fun T => if T = B then w T + a else w T) U =
      partitionWeight w U + a * partitionWeight w (U \ B) := by
  classical
  have hterm (P : Finpartition U) :
      (∏ T ∈ P.parts, if T = B then w T + a else w T) =
        (∏ T ∈ P.parts, w T) + a * (if B ∈ P.parts then ∏ T ∈ P.parts.erase B, w T else 0) := by
    by_cases hB : B ∈ P.parts
    · rw [← Finset.mul_prod_erase _ _ hB, ← Finset.mul_prod_erase (f := w) _ hB, if_pos hB, if_pos rfl]
      have heq : (∏ T ∈ P.parts.erase B, (if T = B then w T + a else w T)) =
          ∏ T ∈ P.parts.erase B, w T := by
        refine Finset.prod_congr rfl fun t ht => ?_
        rw [if_neg (Finset.mem_erase.mp ht).1]
      rw [heq, add_mul]
    · rw [if_neg hB, mul_zero, add_zero]
      refine Finset.prod_congr rfl fun t ht => ?_
      have hne : t ≠ B := fun h => hB (h ▸ ht)
      rw [if_neg hne]
  rw [partitionWeight, partitionWeight]
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, sum_partitions_containing w hb hne]

/-- Giving a block weight zero removes every partition that contains such a block. -/
theorem partitionWeight_filter {R : Type*} [CommSemiring R]
    (w : Finset ι → R) (U : Finset ι) (keep : Finset ι → Prop) :
    (by classical exact partitionWeight (fun T => if keep T then w T else 0) U) =
      (by
        classical
        exact ∑ P ∈ (Finset.univ.filter fun P : Finpartition U => ∀ T ∈ P.parts, keep T),
          ∏ T ∈ P.parts, w T) := by
  classical
  rw [partitionWeight, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P _
  by_cases hP : ∀ T ∈ P.parts, keep T
  · rw [if_pos hP]
    exact Finset.prod_congr rfl fun T hT => if_pos (hP T hT)
  · rw [if_neg hP]
    push Not at hP
    obtain ⟨T, hT, ht⟩ := hP
    exact Finset.prod_eq_zero hT (if_neg ht)

end Chowla

import Chowla.Model.SubsetSums

namespace Chowla

open scoped BigOperators

/-- The combinatorial regrouping in the contraction formula. The block containing the marked
label has weight `w`. Among all other blocks, at most one uses an exceptional weight `d`,
and their regular weights `g` only occur on pairs. -/
theorem marked_pairCompletion {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (U : Finset ι) (m : ι) (hm : m ∉ U) (w g d : Finset ι → R)
    (hg : ∀ B : Finset ι, B.card ≠ 2 → g B = 0) (hd₀ : d ∅ = 0)
    (hd : ∀ B C : Finset ι, B ⊆ U → C ⊆ U → B ≠ C → Disjoint B C → d B * d C = 0) :
    (by classical exact partitionWeight (fun B => if m ∈ B then w B else g B + d B) (insert m U)) =
      (by
        classical
        exact ∑ P ∈ (Finset.univ.filter fun P : Finpartition U =>
          ∀ B ∈ P.parts, B.card = 1 ∨ B.card = 2),
          let S := U \ pairSupport P
          (w (insert m S) + ∑ A ∈ S.powerset, w (insert m A) * d (S \ A)) *
            ∏ B ∈ pairParts P, g B) := by
  classical
  let h := fun B : Finset ι => if m ∈ B then w B else g B + d B
  change partitionWeight h (insert m U) = _
  rw [partitionWeight_marked h (Finset.mem_insert_self _ _), sum_marked_powerset U m hm]
  have ha (A : Finset ι) : (insert m U) \ (insert m A) = U \ A := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    have hh : i = m → i ∉ U := fun he => he ▸ hm
    tauto
  have hpart (B : Finset ι) (hb : B ⊆ U) :
      partitionWeight h B = partitionWeight (fun T => g T + d T) B := by
    unfold partitionWeight
    apply Finset.sum_congr rfl
    intro P _
    apply Finset.prod_congr rfl
    intro T hT
    exact if_neg (fun hT' => hm (hb (P.le hT hT')))
  have he₀ (B : Finset ι) :
      (∑ A ∈ B.powerset.erase ∅, d A * partitionWeight g (B \ A)) =
        ∑ A ∈ B.powerset, d A * partitionWeight g (B \ A) := by
    have hm : ∅ ∈ B.powerset := Finset.mem_powerset.mpr (Finset.empty_subset _)
    simpa only [hd₀, zero_mul, add_zero] using
      (Finset.sum_erase_add B.powerset (fun A => d A * partitionWeight g (B \ A)) hm)
  have he₁ (A : Finset ι) :
      h (insert m A) * partitionWeight h ((insert m U) \ (insert m A)) =
        w (insert m A) * partitionWeight g (U \ A) +
        ∑ B ∈ (U \ A).powerset, (w (insert m A) * d B) * partitionWeight g ((U \ A) \ B) := by
    rw [ha, hpart _ Finset.sdiff_subset, partitionWeight_add_exception g d (U \ A)
      (fun B C hB hC hd' hdis => hd B C (hB.trans Finset.sdiff_subset) (hC.trans Finset.sdiff_subset) hd' hdis),
      he₀, mul_add, Finset.mul_sum]
    simp only [h, Finset.mem_insert_self, if_true, mul_assoc]
  simp_rw [he₁, Finset.sum_add_distrib]
  have hnon (A : Finset ι) (hA : A ∈ U.powerset) : U \ (U \ A) = A :=
    Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hA)
  have hfirst :
      (∑ A ∈ U.powerset, w (insert m A) * partitionWeight g (U \ A)) =
        ∑ T ∈ U.powerset, w (insert m (U \ T)) * partitionWeight g T := by
    rw [sum_powerset_complement U (fun A => w (insert m A) * partitionWeight g (U \ A))]
    exact Finset.sum_congr rfl fun A hA => by rw [hnon A hA]
  have hsecond :
      (∑ A ∈ U.powerset, ∑ B ∈ (U \ A).powerset,
          (w (insert m A) * d B) * partitionWeight g ((U \ A) \ B)) =
        ∑ T ∈ U.powerset, (∑ A ∈ (U \ T).powerset, w (insert m A) * d ((U \ T) \ A)) *
          partitionWeight g T := by
    rw [sum_powerset_complement_rotate U (fun A B T => (w (insert m A) * d B) * partitionWeight g T)]
    simp_rw [Finset.sum_mul]
  rw [hfirst, hsecond, ← Finset.sum_add_distrib]
  simp_rw [← add_mul]
  exact partitionWeight_pairCompletion g
    (fun S => w (insert m S) + ∑ A ∈ S.powerset, w (insert m A) * d (S \ A)) U hg

end Chowla

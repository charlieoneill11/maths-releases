import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Chowla

open scoped BigOperators

/-- A finite product with pairwise-annihilating exceptional weights contains at most one
exceptional factor. This is used for the non-Gaussian blocks of Lemma 25. -/
theorem prod_add_eq_at_most_one_exception {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (S : Finset ι) (g d : ι → R)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → d i * d j = 0) :
    (∏ i ∈ S, (g i + d i)) =
      (∏ i ∈ S, g i) + ∑ j ∈ S, d j * ∏ i ∈ S.erase j, g i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hdS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → d i * d j = 0 := fun i hi j hj =>
      hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
    have hz :
        d a * (∑ j ∈ S, d j * ∏ i ∈ S.erase j, g i) = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      have h := hd a (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun he => ha (he ▸ hj))
      rw [← mul_assoc, h, zero_mul]
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
      Finset.erase_insert ha, ih hdS]
    have hs :
        (∑ j ∈ S, d j * ∏ i ∈ (insert a S).erase j, g i) =
          g a * ∑ j ∈ S, d j * ∏ i ∈ S.erase j, g i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hja : j ≠ a := fun he => ha (he ▸ hj)
      have hErase : (insert a S).erase j = insert a (S.erase j) := by
        ext i
        by_cases hi : i = a
        · simp [hi, hja.symm]
        · simp [hi]
      rw [hErase, Finset.prod_insert (fun hm => ha (Finset.mem_of_mem_erase hm))]
      ac_rfl
    rw [hs, add_mul, mul_add, mul_add, hz, add_zero]
    simp only [add_comm, add_left_comm]

end Chowla

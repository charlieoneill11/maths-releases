import HadwigerNelson.Angular.Range
import HadwigerNelson.Angular.Boxes

namespace HadwigerNelson.Angular

theorem blockSum_eq (t : Segments) (ok : t.Valid) {n w k : Nat} (hn : 0 < n)
    (hk : k*w+w ≤ n) : blockSum t n w k = rangeSum (weightedBin t n) (k*w) w := by
  simp only [blockSum]
  split_ifs with skippedBlock
  · rw [rangeSum_spec]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have lt := Finset.mem_range.mp hj
    apply weightedBin_zero_of_skipped t ok hn
      (i := k*w) (j := k*w+w) (k := k*w+j) <;> first | assumption | omega
  · rfl

theorem rangeSum_by_blocks (t : Segments) (ok : t.Valid) {n w m : Nat} (hn : 0 < n)
    (hm : m*w ≤ n) :
    rangeSum (blockSum t n w) 0 m = rangeSum (weightedBin t n) 0 (m*w) := by
  induction m with
  | zero => simp [rangeSum_spec]
  | succ m ih =>
    have eq : m.succ*w = m*w + w := Nat.succ_mul _ _
    rw [eq] at hm ⊢
    rw [rangeSum_split (blockSum t n w) 0 m 1, rangeSum_split (weightedBin t n), Nat.zero_add, Nat.zero_add]
    have prev := ih (by omega)
    rw [prev]
    have last : rangeSum (blockSum t n w) m 1 = blockSum t n w m := by simp [rangeSum_spec]
    rw [last, blockSum_eq t ok hn hm]

/-- The joined checker covers the same fine bins as the direct angular quadrature. -/
theorem angularSum_spec (profile : Array Nat) {n : Nat} (hn : 0 < n) (hd : 4096 ∣ n) :
    angularSum profile n =
      ∑ j ∈ Finset.range n, weightedBin (tabulate profile CompleteWave.step 11 0) n j := by
  let t := tabulate profile CompleteWave.step 11 0
  change rangeSum (blockSum t n (n/4096)) 0 4096 = _
  have eq : 4096*(n/4096) = n := Nat.mul_div_cancel' hd
  rw [rangeSum_by_blocks t (tabulate_valid _ _ (by decide) _ _) hn (by omega), eq, rangeSum_spec]
  simp only [Nat.zero_add]
  rfl

end HadwigerNelson.Angular

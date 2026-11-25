import HadwigerNelson.Angular.Weights
import HadwigerNelson.Angular.Bound

namespace HadwigerNelson.Angular

/-- One interval contains 128 of the 4096 coarse blocks, altogether 2²³ fine bins. -/
def groupSum (k : Nat) : Nat :=
  let t := tabulate CompleteWave.profile CompleteWave.step 11 0
  rangeSum (blockSum t (2^28) (2^16)) (k*128) 128

def checkGroup (k upper : Nat) : Bool := decide (groupSum k ≤ upper)

theorem rangeSum_from_blocks (t : Segments) (ok : t.Valid) {n w i m : Nat} (hn : 0<n)
    (hi : (i+m)*w ≤ n) :
    rangeSum (blockSum t n w) i m = rangeSum (weightedBin t n) (i*w) (m*w) := by
  have beginLe : i*w ≤ n := (Nat.mul_le_mul_right w (by omega : i ≤ i+m)).trans hi
  have before := rangeSum_by_blocks t ok hn beginLe
  have whole := rangeSum_by_blocks t ok hn hi
  rw [rangeSum_split, Nat.add_mul,rangeSum_split (weightedBin t n)] at whole
  simpa only [Nat.zero_add,before,Nat.add_left_cancel_iff] using whole

/-- The per-shard Boolean bounds a sum of real weighted enclosures over the
specified 2²³ consecutive bins of tan(θ/2). -/
theorem checkGroup_sound {k upper : Nat} (hk : k<32) (ok : checkGroup k upper = true) :
    (∑ i ∈ Finset.range (2^23),
      let j := k*2^23+i
      (boxArea (tabulate CompleteWave.profile CompleteWave.step 11 0)
        (halfAngleBox (2^28) j (j+1)) : ℝ)*(2^28:ℝ)/((2^28:ℝ)^2+(j:ℝ)^2)) ≤ upper := by
  let t := tabulate CompleteWave.profile CompleteWave.step 11 0
  have hg : groupSum k ≤ upper := of_decide_eq_true ok
  change rangeSum (blockSum t (2^28) (2^16)) (k*128) 128 ≤ upper at hg
  have e : (k*128+128)*2^16 ≤ 2^28 := by omega
  rw [rangeSum_from_blocks t (tabulate_valid _ _ (by decide) _ _) (by decide) e,
    rangeSum_spec] at hg
  have heq : k*128*2^16 = k*2^23 := by ring
  rw [heq] at hg
  have total : (∑ i ∈ Finset.range (2^23), (weightedBin t (2^28) (k*2^23+i) : ℝ)) ≤ upper := by
    exact_mod_cast hg
  apply le_trans _ total
  apply Finset.sum_le_sum
  intro i _
  have iw := weightedBin_bound t (by decide : 0 < 2^28) (k*2^23+i)
  simpa only [Nat.cast_pow,Nat.cast_ofNat,pow_two] using iw

attribute [local irreducible] rangeSum tabulate blockSum

theorem angularSum_le_groups (upper : Nat → Nat)
    (ok : ∀ k < 32, checkGroup k (upper k) = true) :
    angularSum CompleteWave.profile (2^28) ≤ ∑ k ∈ Finset.range 32, upper k := by
  let f := blockSum (tabulate CompleteWave.profile CompleteWave.step 11 0) (2^28) (2^16)
  change rangeSum f 0 (32*128) ≤ _
  apply rangeSum_le_of_group_bounds f 32 128 upper
  intro k hk
  exact of_decide_eq_true (ok k hk)

end HadwigerNelson.Angular

import HadwigerNelson.Angular.Partial.Profile
import HadwigerNelson.Angular.Partial.Runtime
import HadwigerNelson.Angular.Weights
import HadwigerNelson.Placement.Proposition12
import Mathlib.Analysis.Real.Pi.Bounds

/-! Adaptive angular quadrature for the partial wave. A zero-area block
bounds every direction in all its fine bins. Other blocks contribute their
individual rounded weighted areas. -/

namespace HadwigerNelson.Angular.Partial
open Arithmetic Wave Placement Set
open scoped BigOperators
noncomputable section

private def coarseArea (w : Walls) (k : ℕ) :=
  area w (halfAngleBox bins (k*blockSize) (k*blockSize+blockSize))

/-- Twice the area estimate for a fine bin, in squared picounits. -/
def adaptiveArea (w : Walls) (j : ℕ) : ℕ :=
  if coarseArea w (j/blockSize) = 0 then 0 else area w (halfAngleBox bins j (j+1))

private def adaptiveWeight (w : Walls) (j : ℕ) : ℕ :=
  if coarseArea w (j/blockSize) = 0 then 0 else weighted w bins j

private theorem weighted_le (w : Walls) (j : ℕ) :
    (area w (halfAngleBox bins j (j+1)) : ℝ)*bins/((bins:ℝ)^2+(j:ℝ)^2) ≤ weighted w bins j := by
  let a := area w (halfAngleBox bins j (j+1))
  have den : (0:Int) < (bins:Int)*bins+(j:Int)*j := rayDen_pos _ (by decide)
  have h := real_le_ceilDiv ((a:Int)*bins) den
  have round : ceilDiv ((a:Int)*bins) ((bins:Int)*bins+(j:Int)*j) ≤ (weighted w bins j : Int) :=
    Int.self_le_toNat _
  have hr : (ceilDiv ((a:Int)*bins) ((bins:Int)*bins+(j:Int)*j) : ℝ) ≤ weighted w bins j := by
    exact_mod_cast round
  push_cast at h
  norm_num only [a,bins,Nat.cast_pow,Nat.cast_ofNat,sq] at h ⊢
  exact h.trans hr

private theorem adaptiveWeight_le (w : Walls) (j : ℕ) :
    (adaptiveArea w j : ℝ)*bins/((bins:ℝ)^2+(j:ℝ)^2) ≤ adaptiveWeight w j := by
  unfold adaptiveArea adaptiveWeight
  split
  · simp
  · exact weighted_le w j

private theorem block_eq (w : Walls) (k : ℕ) :
    block w k = rangeSum (adaptiveWeight w) (k*blockSize) blockSize := by
  have index {i : ℕ} (hi : i < blockSize) : (k*blockSize+i)/blockSize = k := by
    change i<16384 at hi
    change (k*16384+i)/16384=k
    omega
  change (if coarseArea w k = 0 then 0 else rangeSum (weighted w bins) (k*blockSize) blockSize) = _
  by_cases skip : coarseArea w k = 0
  · rw [if_pos skip,rangeSum_spec]
    symm
    exact Finset.sum_eq_zero (fun i hi => by
      rw [adaptiveWeight,index (Finset.mem_range.mp hi),if_pos skip])
  · rw [if_neg skip,rangeSum_spec,rangeSum_spec]
    apply Finset.sum_congr rfl
    intro i hi
    rw [adaptiveWeight,index (Finset.mem_range.mp hi),if_neg skip]

private theorem blocks_eq (w : Walls) (start n : ℕ) :
    rangeSum (block w) start n = rangeSum (adaptiveWeight w) (start*blockSize) (n*blockSize) := by
  induction n with
  | zero => simp [rangeSum_spec]
  | succ n ih =>
    rw [rangeSum_split (block w) start n 1,
      Nat.succ_mul,rangeSum_split (adaptiveWeight w),ih]
    rw [show rangeSum (block w) (start+n) 1 = block w (start+n) by simp [rangeSum_spec],
      block_eq,Nat.add_mul]

private theorem checked_range {k u : ℕ} (ok : checkGroup k u = true) :
    rangeSum (adaptiveWeight walls) (k*groupSize) groupSize ≤ u := by
  have bound : rangeSum (block walls) (k*128) 128 ≤ u := of_decide_eq_true ok
  rw [blocks_eq, Nat.mul_assoc] at bound
  exact bound

/-- One successful group bounds the real angle-weighted areas throughout
its 2²¹ fine bins, including all bins covered by a zero block. -/
theorem checkGroup_real_bound {k u : ℕ} (ok : checkGroup k u = true) :
    (∑ i ∈ Finset.range groupSize, let j := k*groupSize+i
      (adaptiveArea walls j : ℝ)*bins/((bins:ℝ)^2+(j:ℝ)^2)) ≤ u := by
  have h := checked_range ok
  rw [rangeSum_spec] at h
  have hr : (∑ i ∈ Finset.range groupSize, (adaptiveWeight walls (k*groupSize+i) : ℝ)) ≤ u := by
    exact_mod_cast h
  exact (Finset.sum_le_sum (fun i _ => adaptiveWeight_le walls (k*groupSize+i))).trans hr

/-- Every physical angular interval is bounded by its enclosing box. This
unifies skipped-block and single-bin enclosures. -/
def Cover (W : Datum) : Prop :=
  ∀ {i j : ℕ}, i<j → j≤bins → ∀ {θ : ℝ}, θ ∈ Icc (binEdge bins i) (binEdge bins j) →
    W.x*H*directionalMonoProb W (point (Real.cos θ) (Real.sin θ)) ≤
      (area walls (halfAngleBox bins i j) : ℝ)/(2*(10^12:ℝ)^2)

private theorem edgeMono : Monotone (binEdge bins) :=
  monotone_nat_of_le_succ (binEdge_mono bins)

private theorem adaptive_cover {W : Datum} (hc : Cover W) (j : ℕ) (hj : j<bins)
    {θ : ℝ} (hθ : θ∈Icc (binEdge bins j) (binEdge bins (j+1))) :
    W.x*H*directionalMonoProb W (point (Real.cos θ) (Real.sin θ)) ≤
      (adaptiveArea walls j : ℝ)/(2*(10^12:ℝ)^2) := by
  unfold adaptiveArea
  split_ifs with skip
  · let start := j/blockSize*blockSize
    have index : start ≤ j ∧ j+1≤start+blockSize ∧ start+blockSize≤bins ∧ start<start+blockSize := by
      change j < 67108864 at hj
      change j/16384*16384≤j ∧ j+1≤j/16384*16384+16384 ∧
        j/16384*16384+16384≤67108864 ∧ j/16384*16384<j/16384*16384+16384
      omega
    have h := hc (i := start) (j := start+blockSize) index.2.2.2 index.2.2.1
      ⟨(edgeMono index.1).trans hθ.1, hθ.2.trans (edgeMono index.2.1)⟩
    change area walls (halfAngleBox bins start (start+blockSize)) = 0 at skip
    simpa only [skip] using h
  · exact hc (Nat.lt_succ_self _) hj hθ

private theorem normalize (p : ℝ) (h : (314159265358979323846:ℝ)/10^20 ≤ p) :
    (2/(p*(923111560246/10^12)*(1/2))) * (513913267682457543/(10^12:ℝ)^2) ≤
      102782566719698111/145001902327661557000000 := by
  have hp : (0:ℝ) < p := lt_of_lt_of_le (by norm_num) h
  have eq : (2/(p*(923111560246/10^12)*(1/2))) * (513913267682457543/(10^12:ℝ)^2) =
      2*513913267682457543/(923111560246*500000000000*p) := by
    field_simp
    <;> ring
  rw [eq]
  apply (div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0:ℝ) <
    923111560246*500000000000*(314159265358979323846/10^20))
    (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤923111560246*500000000000))).trans
  norm_num

/-- Thirty-two certified groups bound the complete randomized partial-wave
overlap. The integer cap is the floor obtained with Mathlib’s 20-place lower
bound for π. -/
theorem probability_of_groups {W : Datum} (p : Profile W) (hcover : Cover W) (upper : ℕ → ℕ)
    (ok : ∀ k<32, checkGroup k (upper k) = true)
    (hcap : ∑ k ∈ Finset.range 32, upper k ≤ 513913267682457543) :
    meanMonoProb W ≤ 102782566719698111/145001902327661557000000 := by
  let A (j : ℕ) : ℝ := (adaptiveArea walls j : ℝ)/(2*(10^12:ℝ)^2)
  have initial := meanMonoProb_of_bins W bins (by decide) A
    (fun j _ => div_nonneg (Nat.cast_nonneg _) (by norm_num)) (fun j hj _ h => adaptive_cover hcover j hj h)
  have eq : (∑ j ∈ Finset.range bins, A j * (2*(bins:ℝ)/((bins:ℝ)^2+(j:ℝ)^2))) =
      (∑ j ∈ Finset.range bins, ((adaptiveArea walls j : ℝ)*bins/((bins:ℝ)^2+(j:ℝ)^2)))/(10^12:ℝ)^2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [A]
    ring
  have bound : rangeSum (adaptiveWeight walls) 0 bins ≤ 513913267682457543 :=
    (rangeSum_le_of_group_bounds _ 32 groupSize upper (fun k hk => checked_range (ok k hk))).trans hcap
  rw [rangeSum_spec] at bound
  simp only [Nat.zero_add] at bound
  have realBound : (∑ j ∈ Finset.range bins, (adaptiveWeight walls j : ℝ)) ≤ 513913267682457543 := by
    exact_mod_cast bound
  have summed := (Finset.sum_le_sum (s := Finset.range bins) (fun j _ => adaptiveWeight_le walls j)).trans realBound
  rw [eq] at initial
  have hx : 0 < W.x := by linarith [W.x_bounds.1]
  have pos : 0 ≤ 2/(Real.pi*W.x*H) :=
    div_nonneg (by norm_num) (mul_nonneg (mul_nonneg Real.pi_pos.le hx.le) H_pos.le)
  apply (initial.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right summed (by norm_num)) pos)).trans
  rw [p.x]
  exact normalize _ (by linarith only [Real.pi_gt_d20])

end
end HadwigerNelson.Angular.Partial

import LeastPrime.Cited
import LeastPrime.ProofDefs
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-! Divisors and subsets of indexed prime factors. -/

namespace LeastPrime

open Finset Real Set

private theorem sublist_prod_indexed {a l : List ℕ} (h : a.Sublist l) :
    ∃ D : Finset (Fin l.length), a.prod = ∏ i ∈ D, l[i.val] := by
  induction h with
  | slnil => exact ⟨∅, by rw [Finset.prod_empty]; rfl⟩
  | cons p h ih =>
    obtain ⟨D, hD⟩ := ih
    exact ⟨D.map (Fin.succEmb _), by simpa using hD⟩
  | @cons₂ l₁ l₂ p h ih =>
    obtain ⟨D, hD⟩ := ih
    refine ⟨insert 0 (D.map (Fin.succEmb _)), ?_⟩
    have hzero : (0 : Fin (_ + 1)) ∉ D.map (Fin.succEmb _) := by
      simp [Finset.mem_map]
    refine (congrArg (p * ·) hD).trans ?_
    symm
    apply (Finset.prod_insert (f := fun i : Fin (l₂.length + 1) => (p :: l₂)[i.val]) hzero).trans
    simp

private theorem padded_factors (j : ℕ) {n : ℕ} (hn : n ≠ 0) {factors : List ℕ}
    (hperm : factors.Perm n.primeFactorsList) :
    let l := factors ++ List.replicate j 1
    ∃ hle : j ≤ l.length,
      (∀ i : Fin l.length, 0 < l[i.val]) ∧
      (∏ i : Fin l.length, l[i.val]) = n ∧
      (∀ i : Fin j, revealedVector j n factors i =
        log ((l[(Fin.castLEEmb hle i).val] : ℕ) : ℝ) / log n) := by
  let l := factors ++ List.replicate j 1
  have hle : j ≤ l.length := by simp [l]
  refine ⟨hle, ?_, ?_, ?_⟩
  · intro i
    have hm := List.getElem_mem i.isLt
    change l[i.val] ∈ factors ++ List.replicate j 1 at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact (Nat.prime_of_mem_primeFactorsList (hperm.mem_iff.mp hm)).pos
    · have heq := (List.mem_replicate.mp hm).2
      change 0 < l[i.val]
      simp [heq]
  · rw [← List.prod_ofFn, List.ofFn_getElem]
    simp [hperm.prod_eq, Nat.prod_primeFactorsList hn]
  · intro i
    unfold revealedVector
    congr 2
    apply congrArg (fun t : ℕ => (t : ℝ))
    change factors[i.val]?.getD 1 = (factors ++ List.replicate j 1)[i.val]
    by_cases hi : i.val < factors.length
    · rw [List.getElem_append_left hi, List.getElem?_eq_getElem hi]
      rfl
    · rw [List.getElem_append_right (Nat.le_of_not_gt hi),
        List.getElem?_eq_none (Nat.le_of_not_gt hi)]
      simp

private theorem sum_log_shares {k n : ℕ} (f : Fin k → ℕ) (hpos : ∀ i, 0 < f i)
    (D : Finset (Fin k)) :
    (∑ i ∈ D, log (f i : ℝ) / log n) = log ((∏ i ∈ D, f i : ℕ) : ℝ) / log n := by
  rw [← Finset.sum_div, Nat.cast_prod, Real.log_prod]
  intro i _
  exact_mod_cast (hpos i).ne'

private theorem revealed_simplex_and_remainder {j k n : ℕ} (hn : 2 ≤ n)
    (f : Fin k → ℕ) (hpos : ∀ i, 0 < f i) (hprod : ∏ i, f i = n)
    (e : Fin j ↪ Fin k) {v : Fin j → ℝ} (hv : ∀ i, v i = log (f (e i) : ℝ) / log n) :
    let w (i : Fin k) := log (f i : ℝ) / log n
    let R := Finset.univ.map e
    v ∈ simplex j ∧ remainder v = ∑ i ∈ Finset.univ \ R, w i := by
  let w (i : Fin k) := log (f i : ℝ) / log n
  let R := Finset.univ.map e
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog := Real.log_pos hnR
  have hw (i : Fin k) : 0 ≤ w i := by
    have hiR : (1 : ℝ) ≤ f i := by exact_mod_cast hpos i
    exact div_nonneg (log_nonneg hiR) hlog.le
  have hsum : ∑ i, w i = 1 := by
    rw [show (∑ i, w i) = log ((∏ i, f i : ℕ) : ℝ) / log n from sum_log_shares f hpos _,
      hprod, div_self hlog.ne']
  have hV : ∑ i, v i = ∑ i ∈ R, w i := by
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl (fun i _ => hv i)
  have hR : remainder v = ∑ i ∈ Finset.univ \ R, w i := by
    have hs := Finset.sum_sdiff (Finset.subset_univ R) (f := w)
    rw [hsum] at hs
    unfold remainder
    linarith
  refine ⟨?_, hR⟩
  constructor
  · intro i
    rw [hv i]
    refine ⟨hw (e i), ?_⟩
    rw [← hsum]
    exact Finset.single_le_sum (fun k _ => hw k) (Finset.mem_univ _)
  · rw [hV, ← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R) (fun i _ _ => hw i)

/-- A subset sum of revealed log-shares, with or without all unrevealed factors, gives a
divisor of the original integer. -/
theorem divisor_of_revealed {j n : ℕ} (hn : 2 ≤ n) {factors : List ℕ}
    (hperm : factors.Perm n.primeFactorsList) {T : Set ℝ}
    (hE : revealedVector j n factors ∈ E j T) : HasLogDivisorIn n T := by
  classical
  have hn0 : n ≠ 0 := by omega
  let l := factors ++ List.replicate j 1
  obtain ⟨hle, hpos, hprod, hv⟩ := padded_factors j hn0 hperm
  let f (i : Fin l.length) := l[i.val]
  let e := Fin.castLEEmb hle
  let w (i : Fin l.length) := log (f i : ℝ) / log n
  let R := Finset.univ.map e
  obtain ⟨_, hR⟩ := revealed_simplex_and_remainder hn f hpos hprod e hv
  obtain ⟨_, S, ε, hε, hT⟩ := hE
  have hS : ∑ i ∈ S, revealedVector j n factors i = ∑ i ∈ S.map e, w i := by
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl (fun i _ => hv i)
  have hdiv (D : Finset (Fin l.length)) : (∏ i ∈ D, f i) ∈ n.divisors := by
    apply Nat.mem_divisors.mpr
    exact ⟨hprod ▸ Finset.prod_dvd_prod_of_subset _ _ f (Finset.subset_univ D), hn0⟩
  rcases hε with rfl | rfl
  · refine ⟨∏ i ∈ S.map e, f i, hdiv _, ?_⟩
    rw [← sum_log_shares f hpos, ← hS]
    simpa using hT
  · have hdisj : Disjoint (S.map e) (Finset.univ \ R) := by
      apply Finset.disjoint_left.mpr
      intro i hi hi'
      exact (Finset.mem_sdiff.mp hi').2 (Finset.map_subset_map.mpr (Finset.subset_univ S) hi)
    refine ⟨∏ i ∈ (S.map e ∪ (Finset.univ \ R)), f i, hdiv _, ?_⟩
    rw [← sum_log_shares f hpos, Finset.sum_union hdisj, ← hS, ← hR]
    simpa using hT

/-- Every divisor is a subset of the indexed prime factors. Its contribution from the
unrevealed factors lies between zero and the remaining length. -/
theorem revealed_of_divisor {j n : ℕ} (hn : 2 ≤ n) {factors : List ℕ}
    (hperm : factors.Perm n.primeFactorsList) {T : Set ℝ}
    (hd : HasLogDivisorIn n T) : revealedVector j n factors ∈ F j T := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  let l := factors ++ List.replicate j 1
  obtain ⟨hle, hpos, hprod, hv⟩ := padded_factors j hn0 hperm
  let f (i : Fin l.length) := l[i.val]
  let e := Fin.castLEEmb hle
  let w (i : Fin l.length) := log (f i : ℝ) / log n
  let R := Finset.univ.map e
  obtain ⟨hSimplex, hR⟩ := revealed_simplex_and_remainder hn f hpos hprod e hv
  obtain ⟨d, hd, hT⟩ := hd
  have hdvd := (Nat.mem_divisors.mp hd).1
  have hd0 : d ≠ 0 := by
    intro he
    subst d
    exact hn0 (Nat.zero_dvd.mp hdvd)
  have hsub : d.primeFactorsList.Subperm l :=
    (((Nat.primeFactorsList_sublist_of_dvd hdvd hn0).subperm).trans hperm.symm.subperm).trans
      (List.sublist_append_left _ _).subperm
  obtain ⟨dFactors, hdPerm, hdSub⟩ := hsub
  obtain ⟨D, hD⟩ := sublist_prod_indexed hdSub
  have hDProd : ∏ i ∈ D, f i = d := by
    rw [← hD, hdPerm.prod_eq, Nat.prod_primeFactorsList hd0]
  let S : Finset (Fin j) := D.preimage e e.injective.injOn
  have hS : S.map e = D ∩ R := by
    ext i
    simp only [Finset.mem_map, Finset.mem_inter, Finset.mem_preimage, R, S, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨hk, k, rfl⟩
    · rintro ⟨hi, k, rfl⟩
      exact ⟨k, hi, rfl⟩
  have hSsum : ∑ i ∈ S, revealedVector j n factors i = ∑ i ∈ D ∩ R, w i := by
    rw [← hS, Finset.sum_map]
    exact Finset.sum_congr rfl (fun i _ => hv i)
  have hw (i : Fin l.length) : 0 ≤ w i := by
    have hi : (1 : ℝ) ≤ f i := by exact_mod_cast hpos i
    exact div_nonneg (log_nonneg hi) (log_pos hnR).le
  let y := ∑ i ∈ D \ R, w i
  refine ⟨hSimplex, S, y, ⟨Finset.sum_nonneg (fun i _ => hw i), ?_⟩, ?_⟩
  · rw [hR]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.sdiff_subset_sdiff (Finset.subset_univ D) (fun _ hi => hi)) (fun i _ _ => hw i)
  · have hsplit : (∑ i ∈ D \ R, w i) + (∑ i ∈ D ∩ R, w i) = ∑ i ∈ D, w i := by
      have hh := Finset.sum_sdiff (Finset.inter_subset_left (s₁ := D) (s₂ := R)) (f := w)
      have hdiff : D \ (D ∩ R) = D \ R := by
        ext i
        simp only [Finset.mem_sdiff, Finset.mem_inter]
        tauto
      simpa only [hdiff] using hh
    rw [hSsum, add_comm, show y + (∑ i ∈ D ∩ R, w i) = ∑ i ∈ D, w i from hsplit,
      sum_log_shares f hpos, hDProd]
    exact hT

end LeastPrime

import Chowla.Model.Connected

namespace Chowla

open scoped BigOperators

private theorem sole_marked_partition (hs : List FourierProfile) (j : Fin hs.length) :
    partitionSum hs (fun T => j ∈ T) = cumulant hs := by
  classical
  let U : Finset (Fin hs.length) := Finset.univ
  have hj : j ∈ U := Finset.mem_univ _
  have hne : U ≠ ⊥ := by
    change U ≠ ∅
    exact Finset.nonempty_iff_ne_empty.mp ⟨j, hj⟩
  let Q : Finpartition U := Finpartition.indiscrete hne
  have hQ : Q.parts = {U} := rfl
  have hP (P : Finpartition U) (hp : ∀ T ∈ P.parts, j ∈ T) : P = Q := by
    obtain ⟨S, hS, huniq⟩ := P.existsUnique_mem hj
    have hparts : P.parts = {S} := by
      ext T
      simp only [Finset.mem_singleton]
      exact ⟨fun hT => huniq T ⟨hT, hp T hT⟩, fun ht => ht.symm ▸ hS.1⟩
    have hSU : S = U := by simpa only [hparts, Finset.sup_singleton] using P.sup_parts
    apply Finpartition.ext
    rw [hparts, hQ, hSU]
  unfold partitionSum
  calc
    _ = ∑ P ∈ ({Q} : Finset (Finpartition U)), ∏ T ∈ P.parts, blockCumulant hs.get T := by
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext P
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨hP P, by
        rintro rfl T hT
        rw [hQ, Finset.mem_singleton] at hT
        rwa [hT]⟩
    _ = cumulant hs := by
      rw [Finset.sum_singleton, hQ, Finset.prod_singleton]
      unfold blockCumulant U
      exact congrArg cumulant (by rw [Fin.sort_univ, ← List.ofFn_eq_map, List.ofFn_get])

/-- Corollary 26. A single row leaves only the cumulant containing all the labels. -/
theorem innerGRow_eq_cumulant (k : Row) (hk : k.Admissible) (_hne : k.widths ≠ []) :
    innerGRow k = cumulant (convolve H k.profile :: k.widths.map rectangle) := by
  have hA : WidthsAdmissible k.widths := by
    refine ⟨hk.1, ?_⟩
    linarith [hk.2.2.2, radius_nonneg hk.2.1]
  have hB : WidthsAdmissible [] := by simp [WidthsAdmissible]
  have hconn := connected_partitions_of_profile (convolve H k.profile) k.widths []
    (convolve_isProfile H_isProfile hk.2.1) hA hB
  let hs := convolve H k.profile :: (k.widths ++ []).map rectangle
  let j : Fin hs.length := ⟨0, by simp [hs]⟩
  have hkeep : (fun T : Finset (Fin hs.length) =>
      (∃ i ∈ T, i.val = 0) ∨
        ((∃ i ∈ T, 0 < i.val ∧ i.val ≤ k.widths.length) ∧
          (∃ i ∈ T, k.widths.length < i.val))) = (fun T => j ∈ T) := by
    funext T
    apply propext
    have hlt (i : Fin hs.length) : ¬k.widths.length < i.val := by
      have hi := i.isLt
      simp only [hs, List.length_cons, List.length_map, List.append_nil] at hi
      omega
    simp only [hlt, and_false, exists_false, or_false]
    exact ⟨fun ⟨i, hi, hz⟩ => (Fin.ext hz : i = j) ▸ hi, fun hj => ⟨j, hj, rfl⟩⟩
  rw [hkeep, sole_marked_partition hs j] at hconn
  simpa only [innerGRow, wickRow, List.map_nil, wick_nil, mul_one, List.append_nil, hs] using hconn

end Chowla

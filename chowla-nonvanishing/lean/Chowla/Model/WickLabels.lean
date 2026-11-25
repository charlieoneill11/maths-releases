import Chowla.Model.MixedWick

namespace Chowla

open MeasureTheory
open scoped BigOperators

/-- Indices after the marked variable belonging to the first Wick row. -/
def leftLabels (n a : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => 0 < i.val ∧ i.val ≤ a

/-- Indices after the marked variable belonging to the second Wick row. -/
def rightLabels (n a : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => a < i.val

def leftEmbedding (a b n : ℕ) (hn : n = a + b + 1) : Fin a ↪ Fin n where
  toFun i := ⟨i.val + 1, by have hi := i.isLt; omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    simp only at h
    omega

def rightEmbedding (a b n : ℕ) (hn : n = a + b + 1) : Fin b ↪ Fin n where
  toFun i := ⟨a + i.val + 1, by have hi := i.isLt; omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    simp only at h
    omega

theorem map_leftEmbedding (a b n : ℕ) (hn : n = a + b + 1) :
    Finset.univ.map (leftEmbedding a b n hn) = leftLabels n a := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      have hj := j.isLt
      change 0 < j.val + 1 ∧ j.val + 1 ≤ a
      omega⟩
  · intro hi
    have hval := (Finset.mem_filter.mp hi).2
    refine Finset.mem_map.mpr ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change i.val - 1 + 1 = i.val
    omega

theorem map_rightEmbedding (a b n : ℕ) (hn : n = a + b + 1) :
    Finset.univ.map (rightEmbedding a b n hn) = rightLabels n a := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      change a < a + j.val + 1
      omega⟩
  · intro hi
    have hval := (Finset.mem_filter.mp hi).2
    have hlt := i.isLt
    refine Finset.mem_map.mpr ⟨⟨i.val - a - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change a + (i.val - a - 1) + 1 = i.val
    omega

theorem disjoint_label_sets (n a : ℕ) : Disjoint (leftLabels n a) (rightLabels n a) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact (not_lt_of_ge (Finset.mem_filter.mp hi).2.2) (Finset.mem_filter.mp hj).2

/-- The block exclusions obtained by centering and Wick ordering. -/
def KeepWickPartition {n : ℕ} (L R : Finset (Fin n)) (T : Finset (Fin n)) : Prop :=
  ¬(∃ i ∈ L ∪ R, T = {i}) ∧
    ¬(T.card = 2 ∧ (T ⊆ L ∨ T ⊆ R))

theorem wick_moment_partition_eq (h : FourierProfile) (A B : List FourierProfile)
    (hh : ∀ f ∈ h :: (A ++ B), IsProfile f) :
    modelExpectation (stat h * wick A * wick B) =
      partitionSum (h :: (A ++ B))
        (KeepWickPartition (leftLabels (h :: (A ++ B)).length A.length)
          (rightLabels (h :: (A ++ B)).length A.length)) := by
  classical
  let hs := h :: (A ++ B)
  let n := hs.length
  have hn : n = A.length + B.length + 1 := by simp [n, hs]
  let L := leftLabels n A.length
  let R := rightLabels n A.length
  let U : Finset (Fin n) := Finset.univ
  let eL := leftEmbedding A.length B.length n hn
  let eR := rightEmbedding A.length B.length n hn
  let f := hs.get
  have heL : ∀ i : Fin A.length, f (eL i) = A.get i := by
    intro i
    have hi := i.isLt
    have hidx : i.val + 1 < (h :: (A ++ B)).length := by simp; omega
    change (h :: (A ++ B))[i.val + 1]'hidx = A[i.val]
    rw [List.getElem_cons_succ, List.getElem_append_left i.isLt]
  have heR : ∀ i : Fin B.length, f (eR i) = B.get i := by
    intro i
    change (h :: (A ++ B))[A.length + i.val + 1] = B[i.val]
    rw [List.getElem_cons_succ, List.getElem_append_right (by omega)]
    congr 1
    omega
  have hWL : wick A = selectiveWick f (allPairs L) L := by
    rw [wick_eq_selectiveWick]
    change selectiveWick A.get (allPairs Finset.univ) Finset.univ = _
    calc
      _ = selectiveWick f ((allPairs Finset.univ).map (Finset.mapEmbedding eL).toEmbedding)
          (Finset.univ.map eL) :=
        selectiveWick_embedding A.get f eL Finset.univ _ (fun i _ => heL i)
          (fun i _ => hh _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.get_mem _ i))))
      _ = _ := by rw [allPairs_map, show Finset.univ.map eL = L from map_leftEmbedding _ _ _ hn]
  have hWR : wick B = selectiveWick f (allPairs R) R := by
    rw [wick_eq_selectiveWick]
    change selectiveWick B.get (allPairs Finset.univ) Finset.univ = _
    calc
      _ = selectiveWick f ((allPairs Finset.univ).map (Finset.mapEmbedding eR).toEmbedding)
          (Finset.univ.map eR) :=
        selectiveWick_embedding B.get f eR Finset.univ _ (fun i _ => heR i)
          (fun i _ => hh _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.get_mem _ i))))
      _ = _ := by rw [allPairs_map, show Finset.univ.map eR = R from map_rightEmbedding _ _ _ hn]
  have hmark : U \ (L ∪ R) = {⟨0, by omega⟩} := by
    ext i
    simp only [U, L, R, leftLabels, rightLabels, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union,
      Finset.mem_filter, Finset.mem_singleton, true_and, Fin.ext_iff]
    omega
  have hmix := mixed_wick_moment f U L R (allPairs L) (allPairs R) (Finset.subset_univ _)
    (Finset.subset_univ _) (disjoint_label_sets n A.length) (fun i _ => hh _ (List.get_mem _ i))
    (fun _ hT => (Finset.mem_filter.mp hT).2) (fun _ hT => (Finset.mem_filter.mp hT).2)
  have hpoly : mixedWick f U L R (allPairs L) (allPairs R) = stat h * wick A * wick B := by
    rw [mixedWick, hmark, Finset.prod_singleton, ← hWL, ← hWR]
    rfl
  let keep := KeepWickPartition L R
  have hw : mixedCumulant f L R (allPairs L) (allPairs R) = fun T =>
      @ite ℝ (keep T) (Classical.propDecidable _) (blockCumulant f T) 0 := by
    funext T
    simp only [mixedCumulant, allPairs, Finset.mem_filter, Finset.mem_powerset]
    let p := T.card = 2 ∧
      (((T ⊆ L ∧ T.card = 2) ∧ T ⊆ L) ∨ ((T ⊆ R ∧ T.card = 2) ∧ T ⊆ R))
    have he : p ↔ T.card = 2 ∧ (T ⊆ L ∨ T ⊆ R) := by
      unfold p
      tauto
    by_cases hp : p
    · have hk : ¬keep T := fun ht => ht.2 (he.mp hp)
      dsimp only [p] at hp
      simp only [if_pos hp, if_neg hk]
    · dsimp only [p] at hp
      by_cases hs : ∃ i ∈ L ∪ R, T = {i}
      · have hk : ¬keep T := fun ht => ht.1 hs
        simp only [if_neg hp, if_neg hk, selectiveCumulant]
        exact if_pos hs
      · have hk : keep T := ⟨hs, fun h => hp (he.mpr h)⟩
        simp only [if_neg hp, if_pos hk, selectiveCumulant]
        exact if_neg hs
  calc
    _ = modelExpectation (mixedWick f U L R (allPairs L) (allPairs R)) :=
      congrArg modelExpectation hpoly.symm
    _ = partitionWeight (mixedCumulant f L R (allPairs L) (allPairs R)) U := hmix
    _ = partitionWeight (fun T =>
        @ite ℝ (keep T) (Classical.propDecidable _) (blockCumulant f T) 0) U :=
      congrArg (fun w => partitionWeight w U) hw
    _ = partitionSum hs keep := by
      refine (partitionWeight_filter (blockCumulant f) U keep).trans ?_
      unfold partitionSum
      apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext P
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end Chowla

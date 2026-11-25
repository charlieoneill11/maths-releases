import Chowla.Model.ContractionAlgebra

namespace Chowla

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- Join partitions of disjoint label sets. -/
def mergeFinpartition {S T : Finset ι} (P : Finpartition S) (Q : Finpartition T)
    (hST : Disjoint S T) : Finpartition (S ∪ T) where
  parts := P.parts ∪ Q.parts
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr fun B hB C hC hne => by
    rcases Finset.mem_union.mp hB with hB | hB <;> rcases Finset.mem_union.mp hC with hC | hC
    · exact P.disjoint hB hC hne
    · exact hST.mono (P.le hB) (Q.le hC)
    · exact hST.symm.mono (Q.le hB) (P.le hC)
    · exact Q.disjoint hB hC hne
  sup_parts := by
    rw [Finset.sup_union, P.sup_parts, Q.sup_parts]
    rfl
  bot_notMem := by
    intro h
    exact (Finset.mem_union.mp h).elim P.bot_notMem Q.bot_notMem

/-- Complete a partition into pairs on a subset by giving each remaining position its
own singleton. -/
def completePairs {U T : Finset ι} (hTU : T ⊆ U) (P : Finpartition T) : Finpartition U :=
  (mergeFinpartition P (⊥ : Finpartition (U \ T)) disjoint_sdiff_self_right).copy
    (Finset.union_sdiff_of_subset hTU)

@[simp] theorem completePairs_parts {U T : Finset ι} (hTU : T ⊆ U) (P : Finpartition T) :
    (completePairs hTU P).parts = P.parts ∪ (⊥ : Finpartition (U \ T)).parts := rfl

def pairParts {U : Finset ι} (P : Finpartition U) : Finset (Finset ι) :=
  P.parts.filter fun B => B.card = 2

def pairSupport {U : Finset ι} (P : Finpartition U) : Finset ι :=
  (pairParts P).sup id

theorem pairSupport_subset {U : Finset ι} (P : Finpartition U) :
    pairSupport P ⊆ U :=
  Finset.sup_le fun _ hB => P.le (Finset.mem_filter.mp hB).1

def extractPairs {U : Finset ι} (P : Finpartition U) : Finpartition (pairSupport P) :=
  P.ofSubset (Finset.filter_subset _ _) rfl

theorem extractPairs_card {U : Finset ι} (P : Finpartition U) :
    ∀ B ∈ (extractPairs P).parts, B.card = 2 :=
  fun _ hB => (Finset.mem_filter.mp hB).2

theorem pairParts_completePairs {U T : Finset ι} (hTU : T ⊆ U) (P : Finpartition T)
    (hP : ∀ B ∈ P.parts, B.card = 2) : pairParts (completePairs hTU P) = P.parts := by
  unfold pairParts
  rw [completePairs_parts, Finset.filter_union,
    Finset.filter_eq_self.mpr hP, Finset.filter_eq_empty_iff.mpr, Finset.union_empty]
  intro B hB
  obtain ⟨i, _, rfl⟩ := Finpartition.mem_bot_iff.mp hB
  simp

theorem pairSupport_completePairs {U T : Finset ι} (hTU : T ⊆ U) (P : Finpartition T)
    (hP : ∀ B ∈ P.parts, B.card = 2) : pairSupport (completePairs hTU P) = T := by
  rw [pairSupport, pairParts_completePairs hTU P hP, P.sup_parts]

theorem singleton_mem_iff_notMem_pairSupport {U : Finset ι} (P : Finpartition U)
    (hP : ∀ B ∈ P.parts, B.card = 1 ∨ B.card = 2) {i : ι} :
    {i} ∈ P.parts ↔ i ∈ U \ pairSupport P := by
  constructor
  · intro hi
    refine Finset.mem_sdiff.mpr ⟨P.le hi (Finset.mem_singleton_self i), ?_⟩
    intro hs
    obtain ⟨B, hB, hiB⟩ := Finset.mem_sup.mp hs
    have hBm := Finset.mem_filter.mp hB
    have hne : ({i} : Finset ι) ≠ B := by
      intro he
      rw [← he, Finset.card_singleton] at hBm
      simp at hBm
    exact Finset.disjoint_left.mp (P.disjoint hi hBm.1 hne) (Finset.mem_singleton_self i) hiB
  · intro hi
    obtain ⟨hiU, hin⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨B, hBp, _⟩ := P.existsUnique_mem hiU
    rcases hP B hBp.1 with hone | htwo
    · obtain ⟨j, he⟩ := Finset.card_eq_one.mp hone
      have hij : i = j := Finset.mem_singleton.mp (he ▸ hBp.2)
      have heq : B = {i} := he.trans (congrArg singleton hij.symm)
      exact heq ▸ hBp.1
    · exact (hin (Finset.mem_sup.mpr ⟨B, Finset.mem_filter.mpr ⟨hBp.1, htwo⟩, hBp.2⟩)).elim

theorem complete_extractPairs {U : Finset ι} (P : Finpartition U)
    (hP : ∀ B ∈ P.parts, B.card = 1 ∨ B.card = 2) :
    completePairs (pairSupport_subset P) (extractPairs P) = P := by
  apply Finpartition.ext
  rw [completePairs_parts]
  ext B
  change B ∈ pairParts P ∪ (⊥ : Finpartition (U \ pairSupport P)).parts ↔ B ∈ P.parts
  constructor
  · intro hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact (Finset.mem_filter.mp hb).1
    · obtain ⟨i, hi, rfl⟩ := Finpartition.mem_bot_iff.mp hb
      exact (singleton_mem_iff_notMem_pairSupport P hP).mpr hi
  · intro hb
    rcases hP B hb with h₁ | h₂
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h₁
      apply Finset.mem_union_right
      exact Finpartition.mem_bot_iff.mpr
        ⟨i, (singleton_mem_iff_notMem_pairSupport P hP).mp hb, rfl⟩
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hb, h₂⟩

theorem completePairs_card {U T : Finset ι} (hTU : T ⊆ U) (P : Finpartition T)
    (hP : ∀ B ∈ P.parts, B.card = 2) :
    ∀ B ∈ (completePairs hTU P).parts, B.card = 1 ∨ B.card = 2 := by
  intro B hB
  rw [completePairs_parts] at hB
  rcases Finset.mem_union.mp hB with hB | hB
  · exact Or.inr (hP B hB)
  · obtain ⟨i, _, rfl⟩ := Finpartition.mem_bot_iff.mp hB
    exact Or.inl (Finset.card_singleton i)

end Chowla

namespace Chowla

open scoped BigOperators

/-- Regroup complete pairings on subsets as partial matchings on the whole label set. -/
theorem partitionWeight_pairCompletion {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (g : Finset ι → R) (f : Finset ι → R) (U : Finset ι)
    (hg : ∀ T : Finset ι, T.card ≠ 2 → g T = 0) :
    (∑ T ∈ U.powerset, f (U \ T) * partitionWeight g T) =
      (by
        classical
        exact ∑ P ∈ (Finset.univ.filter fun P : Finpartition U =>
          ∀ T ∈ P.parts, T.card = 1 ∨ T.card = 2),
          f (U \ pairSupport P) * ∏ T ∈ pairParts P, g T) := by
  classical
  let K (T : Finset ι) : Finset (Finpartition T) :=
    Finset.univ.filter fun P => ∀ B ∈ P.parts, B.card = 2
  have hkeep (T : Finset ι) : partitionWeight g T =
      ∑ P ∈ K T, ∏ B ∈ P.parts, g B := by
    have hfull := partitionWeight_filter g T (fun B => B.card = 2)
    have he : (fun B => @ite R (B.card = 2) (Classical.propDecidable _) (g B) 0) = g := by
      funext B
      by_cases hB : B.card = 2
      · exact if_pos hB
      · exact (if_neg hB).trans (hg B hB).symm
    refine (congrArg (fun w => partitionWeight w T) he).symm.trans (hfull.trans ?_)
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext P
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
  simp_rw [hkeep, Finset.mul_sum]
  rw [Finset.sum_sigma' U.powerset K
    (fun T (P : Finpartition T) => f (U \ T) * ∏ B ∈ P.parts, g B)]
  let complete (x : Σ T : Finset ι, Finpartition T) (hx : x ∈ U.powerset.sigma K) :=
    completePairs (Finset.mem_powerset.mp (Finset.mem_sigma.mp hx).1) x.2
  refine Finset.sum_bij complete ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, completePairs_card _ _
      (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).2⟩
  · rintro ⟨T, P⟩ hP ⟨S, Q⟩ hQ he
    have hp : ∀ B ∈ P.parts, B.card = 2 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hP).2).2
    have hq : ∀ B ∈ Q.parts, B.card = 2 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hQ).2).2
    have hTS : T = S := by
      have H := congrArg pairSupport he
      unfold complete at H
      rw [pairSupport_completePairs _ _ hp, pairSupport_completePairs _ _ hq] at H
      exact H
    subst S
    have hPQ : P = Q := by
      apply Finpartition.ext
      have H := congrArg pairParts he
      unfold complete at H
      rw [pairParts_completePairs _ _ hp, pairParts_completePairs _ _ hq] at H
      exact H
    subst Q
    rfl
  · intro P hP
    refine ⟨⟨pairSupport P, extractPairs P⟩,
      Finset.mem_sigma.mpr ⟨Finset.mem_powerset.mpr (pairSupport_subset P),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, extractPairs_card P⟩⟩, ?_⟩
    exact complete_extractPairs P (Finset.mem_filter.mp hP).2
  · rintro ⟨T, P⟩ hP
    have hp : ∀ B ∈ P.parts, B.card = 2 := (Finset.mem_filter.mp (Finset.mem_sigma.mp hP).2).2
    unfold complete
    rw [pairSupport_completePairs _ _ hp, pairParts_completePairs _ _ hp]

end Chowla

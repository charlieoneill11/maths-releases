import Chowla.Model.Moments
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Finset.Preimage

namespace Chowla

open Finset MeasureTheory
open scoped BigOperators

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

private def mapPartition (e : ι ↪ κ) {S : Finset ι} (P : Finpartition S) :
    Finpartition (S.map e) where
  parts := P.parts.map (Finset.mapEmbedding e).toEmbedding
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr fun A hA B hB hne => by
    obtain ⟨A', hA', rfl⟩ := Finset.mem_map.mp hA
    obtain ⟨B', hB', rfl⟩ := Finset.mem_map.mp hB
    exact (Finset.disjoint_map e).mpr (P.disjoint hA' hB' fun h => hne (congrArg _ h))
  sup_parts := by
    ext j
    rw [Finset.mem_sup]
    constructor
    · rintro ⟨T, hT, hj⟩
      obtain ⟨A, hA, rfl⟩ := Finset.mem_map.mp hT
      exact Finset.map_subset_map.mpr (P.le hA) hj
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
      obtain ⟨A, hA, hAi⟩ := Finset.mem_sup.mp (P.sup_parts ▸ hi)
      exact ⟨A.map e, Finset.mem_map.mpr ⟨A, hA, rfl⟩, Finset.mem_map.mpr ⟨i, hAi, rfl⟩⟩
  bot_notMem := by
    intro h
    obtain ⟨A, hA, he⟩ := Finset.mem_map.mp h
    exact P.ne_bot hA (Finset.map_eq_empty.mp he)

private noncomputable def embeddingPreimage (e : ι ↪ κ) (A : Finset κ) : Finset ι :=
  A.preimage e e.injective.injOn

omit [DecidableEq ι] [DecidableEq κ] in
private theorem map_embeddingPreimage (e : ι ↪ κ) {S : Finset ι} {A : Finset κ}
    (hA : A ⊆ S.map e) : (embeddingPreimage e A).map e = A := by
  obtain ⟨B, -, rfl⟩ := Finset.subset_map_iff.mp hA
  rw [embeddingPreimage, Finset.preimage_map]

private noncomputable def unmapPartition (e : ι ↪ κ) {S : Finset ι} (P : Finpartition (S.map e)) :
    Finpartition S where
  parts := P.parts.image (embeddingPreimage e)
  supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr fun A hA B hB hne => by
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
    exact Finset.disjoint_preimage (hs := e.injective.injOn) (ht := e.injective.injOn)
      (P.disjoint hA' hB' fun h => hne (congrArg _ h))
  sup_parts := by
    ext i
    rw [Finset.mem_sup]
    constructor
    · rintro ⟨A, hA, hi⟩
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
      have hei : e i ∈ B := by simpa [embeddingPreimage] using hi
      exact (Finset.mem_map' e).mp (P.le hB hei)
    · intro hi
      have hmap : e i ∈ S.map e := (Finset.mem_map' e).mpr hi
      rw [← P.sup_parts] at hmap
      obtain ⟨A, hA, he⟩ := Finset.mem_sup.mp hmap
      refine ⟨embeddingPreimage e A, Finset.mem_image.mpr ⟨A, hA, rfl⟩, ?_⟩
      simpa [embeddingPreimage] using he
  bot_notMem := by
    intro h
    obtain ⟨A, hA, he⟩ := Finset.mem_image.mp h
    have hmap := map_embeddingPreimage e (P.le hA)
    rw [he, bot_eq_empty, Finset.map_empty] at hmap
    exact P.ne_bot hA hmap.symm

/-- Relabelling by an embedding gives a bijection of the partitions of a set and its image. -/
noncomputable def finpartitionEmbedding (e : ι ↪ κ) (S : Finset ι) :
    Finpartition S ≃ Finpartition (S.map e) where
  toFun := mapPartition e
  invFun := unmapPartition e
  left_inv P := by
    ext1
    change (P.parts.map (Finset.mapEmbedding e).toEmbedding).image (embeddingPreimage e) = P.parts
    rw [Finset.map_eq_image, Finset.image_image, Finset.image_congr]
    · exact Finset.image_id
    · intro T _
      change (T.map e).preimage e e.injective.injOn = T
      exact Finset.preimage_map e T
  right_inv P := by
    ext1
    change (P.parts.image (embeddingPreimage e)).map (Finset.mapEmbedding e).toEmbedding = P.parts
    rw [Finset.map_eq_image, Finset.image_image, Finset.image_congr]
    · exact Finset.image_id
    · intro T hT
      exact map_embeddingPreimage e (P.le hT)

@[simp] theorem finpartitionEmbedding_parts (e : ι ↪ κ) (S : Finset ι) (P : Finpartition S) :
    (finpartitionEmbedding e S P).parts = P.parts.map (Finset.mapEmbedding e).toEmbedding := rfl

theorem partitionMoment_embedding {α β : Type*} [LinearOrder α] [LinearOrder β]
    (h : α → FourierProfile) (g : β → FourierProfile)
    (e : α ↪ β) (B : Finset α) (he : ∀ i ∈ B, g (e i) = h i)
    (hh : ∀ i ∈ B, IsProfile (h i)) :
    partitionMoment h B = partitionMoment g (B.map e) := by
  classical
  unfold partitionMoment
  refine Finset.sum_equiv (finpartitionEmbedding e B) (fun _ => by simp) ?_
  intro P _
  rw [finpartitionEmbedding_parts, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro s hs
  exact blockCumulant_map h g e s (fun i hi => he i (P.le hs hi)) (fun i hi => hh i (P.le hs hi))

/-- The labelled version of the monomial identity, for arbitrary finite sets of positions. -/
theorem modelExpectation_prod_stat {α : Type*} [LinearOrder α] (h : α → FourierProfile)
    (S : Finset α) (hh : ∀ i ∈ S, IsProfile (h i)) :
    modelExpectation (∏ i ∈ S, stat (h i)) = partitionMoment h S := by
  classical
  let L := S.sort (· ≤ ·)
  let fs := L.map h
  let e₀ : Fin L.length ↪ α :=
    ⟨L.get, fun _ _ hi => (S.sort_nodup (· ≤ ·)).get_inj_iff.mp hi⟩
  let e : Fin fs.length ↪ α := (finCongr (List.length_map h)).toEmbedding.trans e₀
  have he (i : Fin fs.length) : h (e i) = fs.get i := by
    simp [e, e₀, fs, List.get_eq_getElem]
  have hSet : (Finset.univ : Finset (Fin fs.length)).map e = S := by
    ext i
    constructor
    · intro hi
      obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
      exact (S.mem_sort (· ≤ ·)).mp (List.get_mem L _)
    · intro hi
      have hL : i ∈ L := (S.mem_sort (· ≤ ·)).mpr hi
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hL
      exact Finset.mem_map.mpr ⟨(finCongr (List.length_map h)).symm j, Finset.mem_univ _, by
        change L.get ((finCongr (List.length_map h)) ((finCongr (List.length_map h)).symm j)) = i
        rwa [Equiv.apply_symm_apply]⟩
  have hprod : (fs.map stat).prod = ∏ i ∈ S, stat (h i) := by
    rw [Finset.prod_eq_multiset_prod]
    change (List.map stat (L.map h)).prod = _
    rw [List.map_map, ← Multiset.prod_coe, ← Multiset.map_coe]
    rw [Finset.sort_eq]
    rfl
  have hfs : ∀ f ∈ fs, IsProfile f := by
    intro f hf
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    exact hh i ((S.mem_sort (· ≤ ·)).mp hi)
  rw [← hprod, modelExpectation_monomial_of_isProfile fs hfs]
  have hp := partitionMoment_embedding fs.get h e Finset.univ (fun i _ => he i)
    (fun i _ => hfs _ (List.get_mem _ i))
  rw [hSet] at hp
  exact hp

end Chowla

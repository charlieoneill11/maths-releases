import Chowla.Model.Partitions
import Chowla.Model.PairCompletion

namespace Chowla.Checker

open scoped BigOperators

variable {ι R : Type*} [DecidableEq ι] [AddCommMonoid R]

/-- All candidates for the block of a specified label. -/
def blocksAt (U : Finset ι) (i : ι) : Finset (Finset ι) :=
  U.powerset.filter fun B => i ∈ B

private theorem blockAt_subset {U : Finset ι} {i : ι} (B : blocksAt U i) : B.val ⊆ U :=
  Finset.mem_powerset.mp (Finset.mem_filter.mp B.property).1

private theorem blockAt_mem {U : Finset ι} {i : ι} (B : blocksAt U i) : i ∈ B.val :=
  (Finset.mem_filter.mp B.property).2

private def insertBlockAt {U : Finset ι} {i : ι} (B : blocksAt U i)
    (P : Finpartition (U \ B.val)) : Finpartition U :=
  ((finpartitionWithBlock (blockAt_subset B) (Finset.ne_empty_of_mem (blockAt_mem B))) P).val

private theorem insertBlockAt_mem {U : Finset ι} {i : ι} (B : blocksAt U i)
    (P : Finpartition (U \ B.val)) : B.val ∈ (insertBlockAt B P).parts :=
  ((finpartitionWithBlock (blockAt_subset B) (Finset.ne_empty_of_mem (blockAt_mem B))) P).property

/-- Reindex arbitrary summands by the unique block containing the specified
label and a partition of the remaining labels. -/
theorem sum_partitions_by_block (U : Finset ι) (i : ι) (hi : i ∈ U) (f : Finpartition U → R) :
    (∑ P : Finpartition U, f P) =
      ∑ B : blocksAt U i, ∑ Q : Finpartition (U \ B.val), f (insertBlockAt B Q) := by
  classical
  rw [Finset.sum_sigma' (Finset.univ : Finset (blocksAt U i)) (fun B => Finset.univ)
    (fun B Q => f (insertBlockAt B Q))]
  symm
  refine Finset.sum_bij (fun x _ => insertBlockAt x.1 x.2) ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_univ _
  · rintro ⟨B, Q⟩ _ ⟨C, T⟩ _ h
    change insertBlockAt B Q = insertBlockAt C T at h
    have he : B.val = C.val := by
      by_contra hne
      have hB : B.val ∈ (insertBlockAt B Q).parts := insertBlockAt_mem B Q
      have hC : C.val ∈ (insertBlockAt B Q).parts := by
        rw [h]
        exact insertBlockAt_mem C T
      exact Finset.disjoint_left.mp ((insertBlockAt B Q).disjoint hB hC hne)
        (blockAt_mem B) (blockAt_mem C)
    have hBC : B = C := Subtype.ext he
    subst C
    have hQT : Q = T :=
      (finpartitionWithBlock (blockAt_subset B) (Finset.ne_empty_of_mem (blockAt_mem B))).injective
        (Subtype.ext h)
    subst T
    rfl
  · intro P _
    obtain ⟨B, hB, _⟩ := P.existsUnique_mem hi
    let b : blocksAt U i :=
      ⟨B, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (P.le hB.1), hB.2⟩⟩
    let eqv := finpartitionWithBlock (blockAt_subset b) (Finset.ne_empty_of_mem (blockAt_mem b))
    let q := eqv.symm ⟨P, hB.1⟩
    exact ⟨⟨b, q⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
      congrArg Subtype.val (eqv.apply_symm_apply _)⟩
  · intro _ _
    rfl

private theorem insertBlockAt_parts {U : Finset ι} {i : ι} (B : blocksAt U i)
    (P : Finpartition (U \ B.val)) :
    (insertBlockAt B P).parts = insert B.val P.parts := rfl

private theorem blockAt_notMem_parts {U : Finset ι} {i : ι} (B : blocksAt U i)
    (P : Finpartition (U \ B.val)) : B.val ∉ P.parts := by
  intro hm
  have hi := blockAt_mem B
  exact (Finset.mem_sdiff.mp (P.le hm hi)).2 hi

private theorem insertBlockAt_pairSupport {U : Finset ι} {i : ι} (B : blocksAt U i)
    (P : Finpartition (U \ B.val)) :
    pairSupport (insertBlockAt B P) =
      if B.val.card = 2 then B.val ∪ pairSupport P else pairSupport P := by
  unfold pairSupport pairParts
  rw [insertBlockAt_parts, Finset.filter_insert]
  by_cases h : B.val.card = 2
  · simp only [if_pos h, Finset.sup_insert, id_eq]
    rfl
  · simp only [if_neg h]

private theorem insertBlockAt_unmatched {U : Finset ι} {i : ι} (B : blocksAt U i)
    (P : Finpartition (U \ B.val)) :
    U \ pairSupport (insertBlockAt B P) =
      if B.val.card = 2 then (U \ B.val) \ pairSupport P
      else B.val ∪ ((U \ B.val) \ pairSupport P) := by
  rw [insertBlockAt_pairSupport]
  by_cases h : B.val.card = 2
  · rw [if_pos h, if_pos h]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union, not_or]
    tauto
  · rw [if_neg h, if_neg h]
    ext x
    by_cases hx : x ∈ B.val
    · have hxU := blockAt_subset B hx
      have hnx : x ∉ pairSupport P := fun ht =>
        (Finset.mem_sdiff.mp (pairSupport_subset P ht)).2 hx
      simp [hx, hxU, hnx]
    · simp [hx]

section SupportWeighted

variable {𝕜 : Type*} [CommSemiring 𝕜]

/-- Weighted partition sum with an arbitrary test of the labels outside pair blocks. -/
noncomputable def supportWeighted (w : Finset ι → 𝕜) (f : Finset ι → 𝕜) (U : Finset ι) : 𝕜 :=
  ∑ P : Finpartition U, (∏ B ∈ P.parts, w B) * f (U \ pairSupport P)

/-- Isolate one labelled position. A pair consumes both labels. A singleton
contributes its label to the unmatched input of the residual sum. -/
theorem supportWeighted_by_block (w : Finset ι → 𝕜) (f : Finset ι → 𝕜)
    (U : Finset ι) (i : ι) (hi : i ∈ U) :
    supportWeighted w f U =
      ∑ B : blocksAt U i, w B.val *
        supportWeighted w
          (if B.val.card = 2 then f else fun S => f (B.val ∪ S)) (U \ B.val) := by
  classical
  unfold supportWeighted
  rw [sum_partitions_by_block U i hi]
  apply Finset.sum_congr rfl
  intro B _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P _
  rw [insertBlockAt_parts, Finset.prod_insert (blockAt_notMem_parts B P),
    insertBlockAt_unmatched]
  by_cases h : B.val.card = 2 <;> simp [h, mul_assoc]

/-- The weight of a singleton or a pair crossing a fixed left-label set. -/
noncomputable def crossBlockWeight (L : Finset ι) (w : ι → ι → 𝕜) (B : Finset ι) : 𝕜 :=
  if B.card = 1 then 1
  else if B.card = 2 then
    ∑ a ∈ B.filter (· ∈ L), ∑ b ∈ B.filter (· ∉ L), w a b
  else 0

/-- The two branches of the partial-matching recursion, in finite labelled sets. -/
theorem supportWeighted_cross_left (L : Finset ι) (w : ι → ι → 𝕜) (f : Finset ι → 𝕜)
    (U : Finset ι) (i : ι) (hiU : i ∈ U) (hiL : i ∈ L) :
    supportWeighted (crossBlockWeight L w) f U =
      supportWeighted (crossBlockWeight L w) (fun S => f (insert i S)) (U.erase i) +
        ∑ j ∈ U \ L, w i j * supportWeighted (crossBlockWeight L w) f (U \ {i, j}) := by
  classical
  let G := crossBlockWeight L w
  let term := fun B : Finset ι =>
    G B * supportWeighted G
      (if B.card = 2 then f else fun S => f (B ∪ S)) (U \ B)
  let pair := fun j : ι => ({i, j} : Finset ι)
  let candidates := insert ({i} : Finset ι) ((U \ L).image pair)
  have hsubset : candidates ⊆ blocksAt U i := by
    intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hm
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by simpa using hiU), by simp⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
      have hjU := (Finset.mem_sdiff.mp hj).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (by simp [pair, Finset.insert_subset_iff, hiU, hjU]), by simp [pair]⟩
  have hzeroterm (B : Finset ι) (hB : B ∈ blocksAt U i) (hmiss : B ∉ candidates) :
      term B = 0 := by
    have hiB : i ∈ B := (Finset.mem_filter.mp hB).2
    have hBU : B ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1
    have hone : B.card ≠ 1 := by
      intro h
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h
      have he : i = j := Finset.mem_singleton.mp hiB
      subst j
      exact hmiss (Finset.mem_insert_self ..)
    by_cases htwo : B.card = 2
    · have hright : B.filter (· ∉ L) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro j hjB hnj
        have hij : i ≠ j := fun h => hnj (h ▸ hiL)
        have hp : pair j = B :=
          Finset.eq_of_subset_of_card_le (by simp [pair, Finset.insert_subset_iff, hiB, hjB])
            (by rw [htwo, show (pair j).card = 2 from Finset.card_pair hij])
        exact hmiss (Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨j, Finset.mem_sdiff.mpr ⟨hBU hjB, hnj⟩, hp⟩))
      simp [term, G, crossBlockWeight, hone, hright]
    · simp [term, G, crossBlockWeight, hone, htwo]
  have hdisj : ({i} : Finset ι) ∉ (U \ L).image pair := by
    intro ht
    obtain ⟨j, hj, hjp⟩ := Finset.mem_image.mp ht
    have h : j ∈ ({i} : Finset ι) := hjp ▸ (by simp [pair] : j ∈ pair j)
    exact (Finset.mem_sdiff.mp hj).2 ((Finset.mem_singleton.mp h).symm ▸ hiL)
  have hinj : Set.InjOn pair (↑(U \ L) : Set ι) := by
    intro j hj k hk he
    have h : j ∈ pair k := he ▸ (by simp [pair] : j ∈ pair j)
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with heq | heq
    · exact ((Finset.mem_sdiff.mp hj).2 (heq.symm ▸ hiL)).elim
    · exact heq
  rw [supportWeighted_by_block G f U i hiU]
  change (∑ B : blocksAt U i, term B.val) = _
  rw [Finset.sum_coe_sort, ← Finset.sum_subset hsubset hzeroterm]
  rw [show candidates = insert ({i} : Finset ι) ((U \ L).image pair) from rfl,
    Finset.sum_insert hdisj, Finset.sum_image hinj]
  congr 1
  · simp [term, G, crossBlockWeight, Finset.singleton_union, Finset.sdiff_singleton_eq_erase]
  · apply Finset.sum_congr rfl
    intro j hj
    have hjL : j ∉ L := (Finset.mem_sdiff.mp hj).2
    have hij : i ≠ j := fun h => hjL (h ▸ hiL)
    simp [term, G, crossBlockWeight, pair, Finset.card_pair hij, Finset.filter_insert, Finset.filter_singleton, hiL, hjL]

theorem supportWeighted_congr_test (w : Finset ι → 𝕜) {f g : Finset ι → 𝕜} (U : Finset ι)
    (hfg : ∀ S ⊆ U, f S = g S) : supportWeighted w f U = supportWeighted w g U := by
  unfold supportWeighted
  apply Finset.sum_congr rfl
  intro P _
  rw [hfg _ Finset.sdiff_subset]

/-- With all remaining labels on the right, the only nonzero partition is the
one consisting entirely of singletons. -/
theorem supportWeighted_cross_right (L : Finset ι) (w : ι → ι → 𝕜) (f : Finset ι → 𝕜)
    (U : Finset ι) (hUL : Disjoint U L) :
    supportWeighted (crossBlockWeight L w) f U = f U := by
  classical
  let P₀ : Finpartition U := ⊥
  have hbot (B : Finset ι) (hB : B ∈ P₀.parts) : B.card = 1 := by
    obtain ⟨i, _, rfl⟩ := Finpartition.mem_bot_iff.mp hB
    simp
  have hpair : pairSupport P₀ = ∅ := by
    unfold pairSupport pairParts
    rw [Finset.filter_eq_empty_iff.mpr (by
      intro B hB
      exact fun e => by simp [hbot B hB] at e)]
    rfl
  have hprod : ∏ B ∈ P₀.parts, crossBlockWeight L w B = 1 := by
    exact Finset.prod_eq_one fun B hB => by simp [crossBlockWeight, hbot B hB]
  unfold supportWeighted
  rw [Finset.sum_eq_single_of_mem P₀ (Finset.mem_univ _)]
  · simp [hprod, hpair]
  · intro P _ hne
    have has : ∃ B ∈ P.parts, B.card ≠ 1 := by
      by_contra! h
      apply hne
      ext B
      constructor
      · intro hB
        obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (h B hB)
        exact Finpartition.mem_bot_iff.mpr
          ⟨i, P.le hB (Finset.mem_singleton_self i), rfl⟩
      · intro hB
        obtain ⟨i, hiU, rfl⟩ := Finpartition.mem_bot_iff.mp hB
        obtain ⟨C, hC, _⟩ := P.existsUnique_mem hiU
        obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (h C hC.1)
        have he : i = j := Finset.mem_singleton.mp hC.2
        simpa [he] using hC.1
    obtain ⟨B, hB, hCard⟩ := has
    have hfilter : B.filter (· ∈ L) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro j hj hjL
      exact Finset.disjoint_left.mp hUL (P.le hB hj) hjL
    have hz : crossBlockWeight L w B = 0 := by
      simp [crossBlockWeight, hCard, hfilter]
    rw [Finset.prod_eq_zero hB hz, zero_mul]

end SupportWeighted

end Chowla.Checker

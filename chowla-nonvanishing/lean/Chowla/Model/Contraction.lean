import Chowla.Model.ContractionLabels
import Chowla.Model.MarkedPairCompletion
import Chowla.Model.RectanglePair

namespace Chowla

open scoped BigOperators Topology

private theorem rectangle_cumulant_split (ls : List ℝ) (hlen : 2 ≤ ls.length)
    (hl : ∀ a ∈ ls, a ∈ Set.Icc (0 : ℝ) 1) :
    cumulant (ls.map rectangle) =
      (if ls.length = 2 then 2 * (ls.foldl min 1) ^ 2 else 0) + rectangleTail ls := by
  rcases ls with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · have ha := hl a List.mem_cons_self
    have hb := hl b (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, Nat.reduceAdd,
      if_true, cumulant, List.foldl_cons, List.foldl_nil, rectangleTail, le_refl]
    rw [rectanglePair_gaussian ha.1 hb.1, min_eq_right ha.2]
  · have hn : (a :: b :: c :: cs).length ≠ 2 := by simp
    have hp : 2 ≤ (a :: b :: c :: cs).length := by simp
    rw [if_neg hn, rectangleTail, if_pos hp, zero_add]
    rfl

private theorem side_card {ι : Type*} [DecidableEq ι] {S : Finset ι} {p : ι → Prop}
    (hl : ∃ i ∈ S, p i) (hr : ∃ i ∈ S, ¬p i) : 2 ≤ S.card := by
  obtain ⟨i, hi, hp⟩ := hl
  obtain ⟨j, hj, hq⟩ := hr
  by_contra! hc
  exact hq ((Finset.card_le_one_iff.mp (by omega) hi hj) ▸ hp)

private theorem pairParts_map {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ↪ κ) (V : Finset ι) (P : Finpartition V) :
    pairParts (finpartitionEmbedding e V P) = (pairParts P).map (Finset.mapEmbedding e).toEmbedding := by
  rw [pairParts, finpartitionEmbedding_parts, Finset.filter_map]
  unfold pairParts
  apply congrArg (Finset.map _)
  ext T
  simp only [Finset.mem_filter, Function.comp_apply]
  change T ∈ P.parts ∧ (T.map e).card = 2 ↔ T ∈ P.parts ∧ T.card = 2
  rw [Finset.card_map]

private theorem pairSupport_map {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ↪ κ) (V : Finset ι) (P : Finpartition V) :
    pairSupport (finpartitionEmbedding e V P) = (pairSupport P).map e := by
  unfold pairSupport
  rw [pairParts_map]
  ext i
  constructor
  · intro hi
    obtain ⟨T, hT, hi⟩ := Finset.mem_sup.mp hi
    obtain ⟨S, hS, rfl⟩ := Finset.mem_map.mp hT
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_map.mpr ⟨j, Finset.mem_sup.mpr ⟨S, hS, hj⟩, rfl⟩
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨S, hS, hj⟩ := Finset.mem_sup.mp hj
    exact Finset.mem_sup.mpr ⟨S.map e, Finset.mem_map.mpr ⟨S, hS, rfl⟩,
      Finset.mem_map.mpr ⟨j, hj, rfl⟩⟩

/-- Lemma 25. Apply the pairing expansion to the connected partitions and use the
total support budget to restrict the possible exceptional block. -/
theorem contraction_formula_of_profile (h : FourierProfile) (A B : List ℝ)
    (hh : IsProfile h) (hA : WidthsAdmissible A) (hB : WidthsAdmissible B)
    (hs : radius h + A.sum + B.sum ≤ 2) :
    modelExpectation (stat h * wick (A.map rectangle) * wick (B.map rectangle)) =
      crossMatchingSum h A B := by
  classical
  let C := A ++ B
  let fs := h :: C.map rectangle
  let e := withMarkedLabel h C
  let m := markedLabel h C
  let V : Finset (Fin C.length) := Finset.univ
  let U := V.map e
  let a := markedWidth h C
  let smallCross (T : Finset (Fin C.length)) :=
    (∃ i ∈ T, i.val < A.length) ∧ ∃ i ∈ T, A.length ≤ i.val
  let bigCross (T : Finset (Fin fs.length)) :=
    (∃ i ∈ T, 0 < i.val ∧ i.val ≤ A.length) ∧ ∃ i ∈ T, A.length < i.val
  let connect (T : Finset (Fin fs.length)) := m ∈ T ∨ bigCross T
  let w := blockCumulant fs.get
  let d := fun T => rectangleTail (widthsOn a T)
  let g := fun T => if T.card = 2 ∧ bigCross T then 2 * (widthsOn a T).foldl min 1 ^ 2 else 0
  have hm : m ∉ U := markedLabel_notMem_map h C V
  have huv : insert m U = (Finset.univ : Finset (Fin fs.length)) :=
    (congrArg (insert m) (map_widthLabels_univ h C)).trans (Finset.insert_erase (Finset.mem_univ m))
  have hCrossMap (T : Finset (Fin C.length)) : bigCross (T.map e) ↔ smallCross T := by
    simp only [bigCross, smallCross, Finset.mem_map]
    constructor
    · rintro ⟨⟨i, ⟨j, hj, rfl⟩, _, hi⟩, k, ⟨l, hl, rfl⟩, hk⟩
      change j.val + 1 ≤ A.length at hi
      change A.length < l.val + 1 at hk
      exact ⟨⟨j, hj, by omega⟩, l, hl, by omega⟩
    · rintro ⟨⟨j, hj, hi⟩, l, hl, hk⟩
      exact ⟨⟨e j, ⟨j, hj, rfl⟩, by change 0 < j.val + 1 ∧ j.val + 1 ≤ A.length; omega⟩,
        e l, ⟨l, hl, rfl⟩, by change A.length < l.val + 1; omega⟩
  have hls (i : Fin C.length) : C.get i ∈ Set.Icc (0 : ℝ) 1 := by
    have hi := List.get_mem C i
    rcases List.mem_append.mp hi with ha | hb
    · exact ⟨(hA.1 _ ha).1.le, (hA.1 _ ha).2.le⟩
    · exact ⟨(hB.1 _ hb).1.le, (hB.1 _ hb).2.le⟩
  have hwidthU (i : Fin fs.length) (hi : i ∈ U) : 0 ≤ a i := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    rw [show a (e j) = C.get j from markedWidth_shift h C j]
    exact (hls j).1
  have hsupport : radius h + (∑ i ∈ U, a i) ≤ 2 := by
    have he : (∑ i ∈ U, a i) = C.sum := by
      change (∑ i ∈ V.map e, a i) = C.sum
      rw [Finset.sum_map]
      simp_rw [show ∀ j : Fin C.length, a (e j) = C.get j from markedWidth_shift h C]
      change (∑ i : Fin C.length, C.get i) = C.sum
      rw [← List.sum_ofFn, List.ofFn_get]
    rw [he]
    simpa only [C, List.sum_append, ← add_assoc] using hs
  have hconn : modelExpectation (stat h * wick (A.map rectangle) * wick (B.map rectangle)) =
      partitionSum fs connect := by
    refine (connected_partitions_of_profile h A B hh hA hB).trans ?_
    have he : (fun T : Finset (Fin fs.length) =>
        (∃ i ∈ T, i.val = 0) ∨ bigCross T) = connect := by
      funext T
      apply propext
      unfold connect
      constructor
      · rintro (⟨i, hi, hz⟩ | hc)
        · exact Or.inl ((Fin.ext hz : i = m) ▸ hi)
        · exact Or.inr hc
      · rintro (hmT | hc)
        · exact Or.inl ⟨m, hmT, rfl⟩
        · exact Or.inr hc
    rw [← he]
  have hsplit (T : Finset (Fin fs.length)) :
      (@ite ℝ (connect T) (Classical.propDecidable _) (w T) 0) =
        if m ∈ T then w T else g T + d T := by
    by_cases hmT : m ∈ T
    · have hcon : connect T := Or.inl hmT
      simp only [if_pos hmT, if_pos hcon]
    · have hsub : T ⊆ U := by
        intro i hi
        have hiU : i ∈ insert m U := huv.symm ▸ Finset.mem_univ i
        exact (Finset.mem_insert.mp hiU).resolve_left (fun e => hmT (e ▸ hi))
      obtain ⟨S, _, hST'⟩ := Finset.subset_map_iff.mp hsub
      have hST := hST'.symm
      have hlist : widthsOn a T = widthsOn C.get S := by
        rw [← hST]
        exact widthsOn_map_marked h C S
      by_cases hc : bigCross T
      · have hcon : connect T := Or.inr hc
        simp only [if_neg hmT, if_pos hcon]
        have hcs : smallCross S := (hCrossMap S).mp (hST.symm ▸ hc)
        have hcard : 2 ≤ S.card := side_card hcs.1 (by
          obtain ⟨i, hi, hk⟩ := hcs.2
          exact ⟨i, hi, not_lt.mpr hk⟩)
        have hlen : 2 ≤ (widthsOn C.get S).length := by simpa using hcard
        have hmem : ∀ b ∈ widthsOn C.get S, b ∈ Set.Icc (0 : ℝ) 1 := by
          intro b hb
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
          exact hls i
        have hw : w T = cumulant ((widthsOn C.get S).map rectangle) := by
          change blockCumulant fs.get T = _
          rw [← hST, blockCumulant]
          exact congrArg cumulant (profilesOn_map_marked h C S)
        rw [hw, rectangle_cumulant_split _ hlen hmem]
        simp only [g, d, hlist, hc, and_true, length_widthsOn]
        rw [← hST, Finset.card_map]
      · have hn : ¬connect T := fun hb => hb.elim hmT hc
        have hsc : ¬smallCross S := fun hs => hc (hST ▸ (hCrossMap S).mpr hs)
        have hside : (∀ i ∈ S, i.val < A.length) ∨ (∀ i ∈ S, A.length ≤ i.val) := by
          unfold smallCross at hsc
          push Not at hsc
          by_cases hleft : ∃ i ∈ S, i.val < A.length
          · exact Or.inl (hsc hleft)
          · push Not at hleft
            exact Or.inr hleft
        have hd : rectangleTail (widthsOn C.get S) = 0 :=
          rectangleTail_eq_zero_of_one_row A B hA hB S hside
        simp only [if_neg hmT, if_neg hn, g, d, hc, and_false, if_false, hlist, hd, add_zero]
  have hweight : partitionSum fs connect =
      partitionWeight (fun T => if m ∈ T then w T else g T + d T) (insert m U) := by
    rw [huv]
    calc
      _ = partitionWeight (fun T => @ite ℝ (connect T) (Classical.propDecidable _) (w T) 0)
          (Finset.univ : Finset (Fin fs.length)) := by
        rw [partitionWeight_filter]
        unfold partitionSum
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext P
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      _ = _ := by
        unfold partitionWeight
        apply Finset.sum_congr rfl
        intro P _
        exact Finset.prod_congr rfl (fun T _ => hsplit T)
  have hregular (T : Finset (Fin fs.length)) (hT : T.card ≠ 2) : g T = 0 := by
    dsimp only [g]
    rw [if_neg (fun hc => hT hc.1)]
  have hδ : d ∅ = 0 := by
    change rectangleTail (widthsOn a ∅) = 0
    rw [widthsOn_empty]
    norm_num [rectangleTail]
  have hdis (T Q : Finset (Fin fs.length)) (hT : T ⊆ U) (hQ : Q ⊆ U)
      (_ : T ≠ Q) (hd : Disjoint T Q) : d T * d Q = 0 := by
    exact rectangleTail_mul_disjoint a U hwidthU
      (by linarith [radius_nonneg hh]) hT hQ hd
  rw [hconn, hweight, marked_pairCompletion U m hm w g d hregular hδ hdis]
  have hmarked (T : Finset (Fin fs.length)) (hT : T ⊆ U) :
      w (insert m T) = cumulant (h :: (widthsOn a T).map rectangle) := by
    obtain ⟨S, _, hST⟩ := Finset.subset_map_iff.mp hT
    rw [hST]
    change blockCumulant fs.get (insert m (S.map e)) = _
    rw [blockCumulant_insert_marked, widthsOn_map_marked]
  have hrem (T : Finset (Fin fs.length)) (hT : T ⊆ U) :
      (∑ S ∈ T.powerset, w (insert m S) * d (T \ S)) =
        d T * cumulant [h] +
          ∑ i ∈ T, d (T.erase i) * cumulant [h, rectangle (a i)] := by
    refine (Finset.sum_congr rfl ?_).trans (sum_marked_rectangles_mul_tail hh a U hwidthU hsupport T hT)
    intro S hS
    rw [hmarked S ((Finset.mem_powerset.mp hS).trans hT)]
  have hclean (P : Finpartition U) :
      (let S := U \ pairSupport P;
        (w (insert m S) + ∑ T ∈ S.powerset, w (insert m T) * d (S \ T)) *
          ∏ T ∈ pairParts P, g T) =
      (let S := U \ pairSupport P;
        (∏ T ∈ pairParts P, g T) *
          (cumulant (h :: (widthsOn a S).map rectangle) + d S * cumulant [h] +
            ∑ i ∈ S, d (S.erase i) * cumulant [h, rectangle (a i)])) := by
    dsimp only
    rw [hmarked _ Finset.sdiff_subset, hrem _ Finset.sdiff_subset, ← add_assoc, mul_comm]
  simp_rw [hclean]
  let E := finpartitionEmbedding e V
  let Big := (Finset.univ : Finset (Finpartition U)).filter (fun P =>
    ∀ T ∈ P.parts, T.card = 1 ∨ T.card = 2)
  let BigCross := Big.filter (fun P => ∀ T ∈ pairParts P, bigCross T)
  have hcut : ∀ P ∈ Big, P ∉ BigCross →
      (let S := U \ pairSupport P;
        (∏ T ∈ pairParts P, g T) *
          (cumulant (h :: (widthsOn a S).map rectangle) + d S * cumulant [h] +
            ∑ i ∈ S, d (S.erase i) * cumulant [h, rectangle (a i)])) = 0 := by
    intro P hP hno
    have hn := fun H => hno (Finset.mem_filter.mpr ⟨hP, H⟩)
    change ¬ ∀ T ∈ pairParts P, bigCross T at hn
    push Not at hn
    obtain ⟨T, hT, hc⟩ := hn
    have hg : g T = 0 := by
      change (if T.card = 2 ∧ bigCross T then _ else _) = _
      rw [if_neg (fun hp => hc hp.2)]
    dsimp only
    rw [Finset.prod_eq_zero hT hg, zero_mul]
  let term (P : Finpartition U) :=
    let S := U \ pairSupport P
    (∏ T ∈ pairParts P, g T) *
      (cumulant (h :: (widthsOn a S).map rectangle) + d S * cumulant [h] +
        ∑ i ∈ S, d (S.erase i) * cumulant [h, rectangle (a i)])
  calc
    _ = ∑ P ∈ Big, term P := by
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext P
      simp only [Big, Finset.mem_filter, Finset.mem_univ, true_and]
    _ = ∑ P ∈ BigCross, term P :=
      (Finset.sum_subset (Finset.filter_subset _ _) hcut).symm
    _ = crossMatchingSum h A B := ?_
  symm
  unfold crossMatchingSum
  dsimp only
  refine Finset.sum_equiv E ?_ ?_
  · intro P
    have hparts : (E P).parts = P.parts.map (Finset.mapEmbedding e).toEmbedding :=
      finpartitionEmbedding_parts e V P
    have hpairs : pairParts (E P) = (pairParts P).map (Finset.mapEmbedding e).toEmbedding :=
      pairParts_map e V P
    simp only [BigCross, Big, Finset.mem_filter, Finset.mem_univ, true_and, hparts,
      hpairs, Finset.mem_map]
    constructor
    · intro hp
      refine ⟨?_, ?_⟩
      · rintro T ⟨S, hS, rfl⟩
        change (S.map e).card = 1 ∨ (S.map e).card = 2
        rw [Finset.card_map]
        exact (hp S hS).imp id And.left
      · rintro T ⟨S, hS, rfl⟩
        obtain ⟨hpS, hcS⟩ := Finset.mem_filter.mp hS
        rcases hp S hpS with hone | hcross
        · omega
        · exact (hCrossMap S).mpr hcross.2
    · rintro ⟨hp, hpc⟩ T hT
      have he : (T.map e).card = 1 ∨ (T.map e).card = 2 :=
        hp _ ⟨T, hT, rfl⟩
      rw [Finset.card_map] at he
      refine he.imp id (fun hc => ⟨hc, ?_⟩)
      exact (hCrossMap T).mp (hpc _ ⟨T, Finset.mem_filter.mpr ⟨hT, hc⟩, rfl⟩)
  · intro P hP
    have hp : ∀ T ∈ P.parts, T.card = 1 ∨ (T.card = 2 ∧ smallCross T) := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, smallCross] using hP
    let S := V \ pairSupport P
    have hS : (V.filter fun i => ∃ pair ∈ P.parts, pair = {i}) = S := by
      ext i
      simp only [Finset.mem_filter, V, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨T, hT, rfl⟩
        exact (singleton_mem_iff_notMem_pairSupport P (fun T hT => (hp T hT).imp id And.left)).mp hT
      · intro hi
        exact ⟨_, (singleton_mem_iff_notMem_pairSupport P
          (fun T hT => (hp T hT).imp id And.left)).mpr hi, rfl⟩
    have hmapS : U \ pairSupport (E P) = S.map e := by
      change V.map e \ pairSupport (finpartitionEmbedding e V P) = (V \ pairSupport P).map e
      rw [pairSupport_map, Finset.map_sdiff]
    have hprod : (∏ T ∈ pairParts (E P), g T) =
        ∏ T ∈ P.parts, if T.card = 2 then 2 * (widthsOn C.get T).foldl min 1 ^ 2 else 1 := by
      change (∏ T ∈ pairParts (finpartitionEmbedding e V P), g T) = _
      rw [pairParts_map, Finset.prod_map]
      simp only [pairParts, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro T hT
      by_cases hc : T.card = 2
      · have hcr : smallCross T := ((hp T hT).resolve_left (by omega)).2
        have hg : (T.map e).card = 2 ∧ bigCross (T.map e) :=
          ⟨(Finset.card_map e).trans hc, (hCrossMap T).mpr hcr⟩
        simp only [if_pos hc]
        change (if (T.map e).card = 2 ∧ bigCross (T.map e) then
          2 * (widthsOn a (T.map e)).foldl min 1 ^ 2 else 0) = _
        rw [if_pos hg, widthsOn_map_marked]
      · simp only [if_neg hc]
    have htail (T : Finset (Fin C.length)) : d (T.map e) = rectangleTail (widthsOn C.get T) := by
      change rectangleTail (widthsOn a (T.map e)) = _
      rw [widthsOn_map_marked]
    have hsingle :
        (∑ i ∈ S.map e, d ((S.map e).erase i) * cumulant [h, rectangle (a i)]) =
        ∑ i ∈ S, rectangleTail (widthsOn C.get (S.erase i)) * cumulant [h, rectangle (C.get i)] := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i _
      simp only [← Finset.map_erase, htail, e, a, markedWidth_shift]
    change (_ *
      (cumulant (h :: (widthsOn C.get (V.filter fun i => ∃ pair ∈ P.parts, pair = {i})).map rectangle)
        + _ + _)) = _
    dsimp only [term]
    rw [hS, hmapS, hprod, widthsOn_map_marked, htail, hsingle]
    rfl

theorem contraction_formula (h : FourierProfile) (A B : List ℝ)
    (hh : IsProfile h) (_hcont : ContinuousAt h 0)
    (hA : WidthsAdmissible A) (hB : WidthsAdmissible B)
    (hs : radius h + A.sum + B.sum ≤ 2) :
    modelExpectation (stat h * wick (A.map rectangle) * wick (B.map rectangle)) =
      crossMatchingSum h A B :=
  contraction_formula_of_profile h A B hh hA hB hs

end Chowla

import Chowla.Model.Embedding
import Chowla.Model.Partitions

namespace Chowla

open MeasureTheory MvPolynomial
open scoped BigOperators

theorem modelExpectation_sub (P Q : Model) :
    modelExpectation (P - Q) = modelExpectation P - modelExpectation Q := by
  simp only [modelExpectation_eq_linear, map_sub]

theorem modelExpectation_C_mul (a : ℝ) (P : Model) :
    modelExpectation (C a * P) = a * modelExpectation P := by
  simp only [modelExpectation_eq_linear]
  change modelExpectationLinear (algebraMap ℝ Model a * P) = a * modelExpectationLinear P
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem blockCumulant_singleton {ι : Type*} [LinearOrder ι] (h : ι → FourierProfile) (i : ι) :
    blockCumulant h {i} = cumulant [h i] := by
  simp [blockCumulant]

noncomputable def selectiveStat {ι : Type*} [DecidableEq ι] (h : ι → FourierProfile)
    (Z : Finset ι) (i : ι) : Model :=
  if i ∈ Z then centered (h i) else stat (h i)

noncomputable def selectiveCumulant {ι : Type*} [LinearOrder ι] (h : ι → FourierProfile)
    (Z : Finset ι) (B : Finset ι) : ℝ := by
  classical
  exact if ∃ i ∈ Z, B = {i} then 0 else blockCumulant h B

/-- Centering a specified set of generators deletes their singleton blocks from the
moment–cumulant sum. -/
theorem selective_moment {ι : Type*} [LinearOrder ι] (h : ι → FourierProfile)
    (Z U : Finset ι) (hZU : Z ⊆ U) (hh : ∀ i ∈ U, IsProfile (h i)) :
    modelExpectation (∏ i ∈ U, selectiveStat h Z i) =
      partitionWeight (selectiveCumulant h Z) U := by
  classical
  induction Z using Finset.induction_on generalizing U with
  | empty =>
    simp only [selectiveStat, Finset.notMem_empty, if_false]
    rw [modelExpectation_prod_stat h U hh]
    unfold partitionMoment partitionWeight selectiveCumulant
    simp
  | @insert i Z hi ih =>
    have hiU : i ∈ U := hZU (Finset.mem_insert_self _ _)
    have hZU' : Z ⊆ U.erase i := by
      intro j hj
      exact Finset.mem_erase.mpr ⟨fun hji => hi (hji ▸ hj), hZU (Finset.mem_insert_of_mem hj)⟩
    have hZU'' : Z ⊆ U := fun j hj => hZU (Finset.mem_insert_of_mem hj)
    let w := blockCumulant h {i}
    have hiw : w = cumulant [h i] := blockCumulant_singleton h i
    have hstat_eq (j : ι) (hj : j ∈ U.erase i) :
        selectiveStat h (insert i Z) j = selectiveStat h Z j := by
      have hji := (Finset.mem_erase.mp hj).1
      simp [selectiveStat, hji]
    have hpoly :
        (∏ j ∈ U, selectiveStat h (insert i Z) j) =
          (∏ j ∈ U, selectiveStat h Z j) -
            C w * ∏ j ∈ U.erase i, selectiveStat h Z j := by
      rw [← Finset.mul_prod_erase _ _ hiU, ← Finset.mul_prod_erase (f := selectiveStat h Z) _ hiU]
      have heq : (∏ j ∈ U.erase i, selectiveStat h (insert i Z) j) =
          ∏ j ∈ U.erase i, selectiveStat h Z j :=
        Finset.prod_congr rfl hstat_eq
      rw [heq, hiw]
      simp [selectiveStat, hi, centered, sub_mul]
    have hw :
        selectiveCumulant h (insert i Z) =
          fun B => if B = {i} then selectiveCumulant h Z B + (-w) else selectiveCumulant h Z B := by
      funext B
      by_cases hB : B = {i}
      · subst B
        simp [selectiveCumulant, hi, w]
      · simp [selectiveCumulant, hB]
    have hU : U.erase i = U \ {i} := by
      ext j
      simp [and_comm]
    rw [hpoly, modelExpectation_sub, modelExpectation_C_mul,
      ih U hZU'' hh,
      ih (U.erase i) hZU' (fun j hj => hh j (Finset.erase_subset _ _ hj)),
      hw, partitionWeight_update _ (-w) (Finset.singleton_subset_iff.mpr hiU)
        (Finset.singleton_ne_empty _), hU]
    ring

noncomputable def partitionSum (hs : List FourierProfile)
    (keep : Finset (Fin hs.length) → Prop) : ℝ := by
  classical
  exact ∑ π ∈ (Finset.univ : Finset (Finpartition (Finset.univ : Finset (Fin hs.length)))).filter
      (fun π => ∀ B ∈ π.parts, keep B),
    ∏ B ∈ π.parts, cumulant ((B.sort (· ≤ ·)).map hs.get)

/-- Equation (11). The marked generator is kept uncentered. -/
theorem centered_moment (h : FourierProfile) (hs : List FourierProfile)
    (hh : ∀ g ∈ h :: hs, IsProfile g ∧ ContinuousAt g 0) :
    modelExpectation (stat h * (hs.map centered).prod) =
      partitionSum (h :: hs) (fun B => B.card ≠ 1 ∨ ∃ i ∈ B, i.val = 0) := by
  classical
  let U : Finset (Fin (h :: hs).length) := Finset.univ
  let Z := U.erase 0
  let f := (h :: hs).get
  have hmom := selective_moment f Z U (Finset.erase_subset _ _)
    (fun i _ => (hh _ (List.get_mem _ i)).1)
  have hs' : (hs.map centered).prod = ∏ i : Fin hs.length, centered (hs.get i) := by
    have hf : List.ofFn (centered ∘ hs.get) = hs.map centered := by
      rw [← List.map_ofFn, List.ofFn_get]
    exact (congrArg List.prod hf).symm.trans List.prod_ofFn
  have hpoly : (∏ i ∈ U, selectiveStat f Z i) = stat h * (hs.map centered).prod := by
    rw [hs']
    change (∏ i : Fin (hs.length + 1), selectiveStat f Z i) = _
    rw [Fin.prod_univ_succ]
    have h0 : selectiveStat f Z 0 = stat h := by
      unfold selectiveStat
      exact if_neg (Finset.notMem_erase _ _)
    have hsuc (i : Fin hs.length) : selectiveStat f Z i.succ = centered (hs.get i) := by
      have hm : i.succ ∈ Z := Finset.mem_erase.mpr ⟨Fin.succ_ne_zero i, Finset.mem_univ _⟩
      unfold selectiveStat
      exact if_pos hm
    exact congrArg₂ (· * ·) h0 (Finset.prod_congr rfl fun i _ => hsuc i)
  let keep : Finset (Fin (h :: hs).length) → Prop := fun T =>
    T.card ≠ 1 ∨ ∃ i ∈ T, i.val = 0
  have hweights : selectiveCumulant f Z = fun T =>
      @ite ℝ (keep T) (Classical.propDecidable _) (blockCumulant f T) 0 := by
    funext T
    have hiff : (∃ i ∈ Z, T = {i}) ↔ ¬(T.card ≠ 1 ∨ ∃ i ∈ T, i.val = 0) := by
      simp only [not_or, not_not]
      constructor
      · rintro ⟨i, hi, rfl⟩
        have hne : i ≠ 0 := (Finset.mem_erase.mp hi).1
        simp only [Finset.card_singleton, true_and, Finset.mem_singleton, exists_eq_left]
        exact fun hz => hne (Fin.ext hz)
      · rintro ⟨hT, hnot⟩
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hT
        refine ⟨i, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, hi⟩
        intro he
        apply hnot
        exact ⟨i, hi ▸ Finset.mem_singleton_self _, by simp [he]⟩
    by_cases hp : keep T
    · exact (show selectiveCumulant f Z T = blockCumulant f T by
          rw [selectiveCumulant, if_neg (fun hbad => hiff.mp hbad hp)]).trans (if_pos hp).symm
    · exact (show selectiveCumulant f Z T = 0 by
          rw [selectiveCumulant, if_pos (hiff.mpr hp)]).trans (if_neg hp).symm
  calc
    modelExpectation (stat h * (hs.map centered).prod) =
        modelExpectation (∏ i ∈ U, selectiveStat f Z i) := congrArg modelExpectation hpoly.symm
    _ = partitionWeight (selectiveCumulant f Z) U := hmom
    _ = partitionWeight (fun T =>
        @ite ℝ (keep T) (Classical.propDecidable _) (blockCumulant f T) 0) U :=
      congrArg (fun w => partitionWeight w U) hweights
    _ = partitionSum (h :: hs) keep := by
      refine (partitionWeight_filter (blockCumulant f) U keep).trans ?_
      unfold partitionSum
      apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext P
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end Chowla

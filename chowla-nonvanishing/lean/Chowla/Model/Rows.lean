import Chowla.Model.Extremal
import Chowla.Model.Embedding

namespace Chowla

open MeasureTheory Set
open scoped BigOperators

theorem rectangle_hasRadiusAtMost {a : ℝ} (ha : 0 ≤ a) : HasRadiusAtMost (rectangle a) a := by
  refine ⟨ha, ?_⟩
  filter_upwards with u hu
  simp [rectangle, hu]

@[simp] theorem wick_nil : wick [] = 1 := by
  classical
  let U : Finset (Fin 0) := Finset.univ
  have hempty : U = ∅ := Finset.eq_empty_of_forall_notMem (fun i _ => Fin.elim0 i)
  have hparts (P : Finpartition U) : P.parts = ∅ :=
    Finpartition.parts_eq_empty_iff.mpr hempty
  have hU : (Finset.univ : Finset (Finpartition U)) = {⊥} := by
    ext P
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Finpartition.ext ((hparts P).trans (hparts ⊥).symm)
  unfold wick
  change (∑ P ∈ (Finset.univ : Finset (Finpartition U)).filter _,
    ∏ B ∈ P.parts, _) = _
  rw [hU]
  calc
    _ = ∑ P ∈ ({⊥} : Finset (Finpartition U)), (1 : Model) := by
      refine Finset.sum_congr ?_ (fun P _ => by rw [hparts P, Finset.prod_empty])
      ext P
      refine ⟨fun h => (Finset.mem_filter.mp h).1, fun h => ?_⟩
      exact Finset.mem_filter.mpr ⟨h, fun B hB => by
        rw [hparts P] at hB
        exact (Finset.notMem_empty B hB).elim⟩
    _ = 1 := Finset.sum_singleton _ _

private theorem parts_singleton_nat (P : Finpartition ({0} : Finset ℕ)) :
    P.parts = {{0}} := by
  ext B
  simp only [Finset.mem_singleton]
  constructor
  · intro hB
    have hne : B ≠ ∅ := P.ne_bot hB
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hzero : i = 0 := Finset.mem_singleton.mp (P.le hB hi)
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hzero ▸ hi, ?_⟩
    intro j hj
    exact Finset.mem_singleton.mp (P.le hB hj)
  · intro hB
    subst B
    obtain ⟨T, hT, _⟩ := P.existsUnique_mem (Finset.mem_singleton_self (0 : ℕ))
    have hEq : T = {0} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hT.2, fun j hj => Finset.mem_singleton.mp (P.le hT.1 hj)⟩
    exact Eq.mp (congrArg (· ∈ P.parts) hEq) hT.1

theorem modelExpectation_singleton (h : FourierProfile) (hh : IsProfile h) :
    modelExpectation (stat h) = cumulant [h] := by
  classical
  have hm := modelExpectation_prod_stat (fun _ : ℕ => h) {0} (fun _ _ => hh)
  rw [Finset.prod_singleton] at hm
  letI : Unique (Finpartition ({0} : Finset ℕ)) := ⟨⟨⊥⟩, fun P => Finpartition.ext
    ((parts_singleton_nat P).trans (parts_singleton_nat ⊥).symm)⟩
  rw [hm, partitionMoment]
  simp [parts_singleton_nat, blockCumulant]

theorem innerGRow_nil (k : Row) (hk : k.Admissible) (hwidths : k.widths = []) :
    innerGRow k = 0 := by
  have hRadius : HasRadiusAtMost k.profile 1 :=
    (hasRadiusAtMost_radius hk.2.1).mono (by simpa [hwidths] using hk.2.2.2)
  rw [innerGRow, wickRow, hwidths, List.map_nil, wick_nil, mul_one,
    modelExpectation_singleton _ (convolve_isProfile H_isProfile hk.2.1),
    extremal_cumulant _ hk.2.1 hRadius, hk.2.2.1, mul_zero]

end Chowla

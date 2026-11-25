import Chowla.Model.PairCompletion
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace Chowla

open scoped BigOperators

/-- Cycle the three disjoint subsets consisting of a chosen set, a second set from its complement,
and the rest. -/
theorem sum_powerset_complement_rotate {ι R : Type*} [DecidableEq ι] [AddCommMonoid R]
    (U : Finset ι) (f : Finset ι → Finset ι → Finset ι → R) :
    (∑ A ∈ U.powerset, ∑ B ∈ (U \ A).powerset, f A B ((U \ A) \ B)) =
      ∑ C ∈ U.powerset, ∑ A ∈ (U \ C).powerset, f A ((U \ C) \ A) C := by
  classical
  let K := fun S : Finset ι => (U \ S).powerset
  rw [Finset.sum_sigma' U.powerset K (fun A B => f A B ((U \ A) \ B)),
      Finset.sum_sigma' U.powerset K (fun C A => f A ((U \ C) \ A) C)]
  have hc (A B : Finset ι) (hA : A ⊆ U) (hB : B ⊆ U \ A) :
      (U \ ((U \ A) \ B)) \ A = B := by
    ext x
    simp only [Finset.mem_sdiff]
    have ha : x ∈ A → x ∈ U := fun h => hA h
    have hb : x ∈ B → x ∈ U ∧ x ∉ A := fun h => Finset.mem_sdiff.mp (hB h)
    tauto
  have hd (C A : Finset ι) (hC : C ⊆ U) (hA : A ⊆ U \ C) :
      (U \ A) \ ((U \ C) \ A) = C := by
    ext x
    simp only [Finset.mem_sdiff]
    have h₁ : x ∈ C → x ∈ U := fun h => hC h
    have h₂ : x ∈ A → x ∈ U ∧ x ∉ C := fun h => Finset.mem_sdiff.mp (hA h)
    tauto
  refine Finset.sum_bij (fun x _ => ⟨(U \ x.1) \ x.2, x.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨A, B⟩ h
    have hA : A ⊆ U := Finset.mem_powerset.mp (Finset.mem_sigma.mp h).1
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.sdiff_subset.trans Finset.sdiff_subset),
      Finset.mem_powerset.mpr ?_⟩
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hA hx, fun hy => (Finset.mem_sdiff.mp ((Finset.mem_sdiff.mp hy).1)).2 hx⟩
  · rintro ⟨A, B⟩ h ⟨A', B'⟩ h' he
    have hA : A ⊆ U := Finset.mem_powerset.mp (Finset.mem_sigma.mp h).1
    have hB : B ⊆ U \ A := Finset.mem_powerset.mp (Finset.mem_sigma.mp h).2
    have hA' : A' ⊆ U := Finset.mem_powerset.mp (Finset.mem_sigma.mp h').1
    have hB' : B' ⊆ U \ A' := Finset.mem_powerset.mp (Finset.mem_sigma.mp h').2
    have h₁ : (U \ A) \ B = (U \ A') \ B' :=
      congrArg (fun t : Σ _ : Finset ι, Finset ι => t.1) he
    have h₂ : A = A' := congrArg (fun t : Σ _ : Finset ι, Finset ι => t.2) he
    have heq : B = B' := by
      rw [← hc A B hA hB, ← hc A' B' hA' hB', h₁, h₂]
    subst A' B'
    rfl
  · rintro ⟨C, A⟩ h
    have hC : C ⊆ U := Finset.mem_powerset.mp (Finset.mem_sigma.mp h).1
    have hA : A ⊆ U \ C := Finset.mem_powerset.mp (Finset.mem_sigma.mp h).2
    refine ⟨⟨A, (U \ C) \ A⟩, ?_, ?_⟩
    · exact Finset.mem_sigma.mpr ⟨Finset.mem_powerset.mpr (hA.trans Finset.sdiff_subset),
        Finset.mem_powerset.mpr (fun x hx => Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1, (Finset.mem_sdiff.mp hx).2⟩)⟩
    · exact congrArg (fun T : Finset ι => (⟨T, A⟩ : Σ _ : Finset ι, Finset ι)) (hd C A hC hA)
  · rintro ⟨A, B⟩ h
    have hA : A ⊆ U := Finset.mem_powerset.mp (Finset.mem_sigma.mp h).1
    have hB : B ⊆ U \ A := Finset.mem_powerset.mp (Finset.mem_sigma.mp h).2
    exact congrArg (fun T => f A T ((U \ A) \ B)) (hc A B hA hB).symm

end Chowla

namespace Chowla

open scoped BigOperators

/-- Reindex subsets that contain the marked position by deleting that position. -/
theorem sum_marked_powerset {ι R : Type*} [DecidableEq ι] [AddCommMonoid R]
    (U : Finset ι) (m : ι) (hm : m ∉ U) (f : Finset ι → R) :
    (∑ A ∈ ((insert m U).powerset.filter fun A => m ∈ A), f A) =
      ∑ A ∈ U.powerset, f (insert m A) := by
  classical
  refine Finset.sum_bij (fun A _ => A.erase m) ?_ ?_ ?_ ?_
  · intro A hA
    have hs := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
    apply Finset.mem_powerset.mpr
    intro i hi
    exact (Finset.mem_insert.mp (hs (Finset.mem_erase.mp hi).2)).resolve_left (Finset.mem_erase.mp hi).1
  · intro A hA B hB he
    change A.erase m = B.erase m at he
    rw [← Finset.insert_erase (Finset.mem_filter.mp hA).2,
      ← Finset.insert_erase (Finset.mem_filter.mp hB).2, he]
  · intro A hA
    have hs := Finset.mem_powerset.mp hA
    refine ⟨insert m A, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.mem_insert_self _ _⟩, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hs hi)
    · exact Finset.erase_insert (fun h => hm (hs h))
  · intro A hA
    rw [Finset.insert_erase (Finset.mem_filter.mp hA).2]

/-- Complementation permutes the subsets of a fixed finite set. -/
theorem sum_powerset_complement {ι R : Type*} [DecidableEq ι] [AddCommMonoid R]
    (U : Finset ι) (f : Finset ι → R) :
    (∑ A ∈ U.powerset, f A) = ∑ A ∈ U.powerset, f (U \ A) := by
  classical
  refine Finset.sum_bij (fun A _ => U \ A) ?_ ?_ ?_ ?_
  · intro A _
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro A hA B hB h
    change U \ A = U \ B at h
    have ha := Finset.mem_powerset.mp hA
    have hb := Finset.mem_powerset.mp hB
    rw [← Finset.sdiff_sdiff_eq_self ha, h, Finset.sdiff_sdiff_eq_self hb]
  · intro A hA
    exact ⟨U \ A, Finset.mem_powerset.mpr Finset.sdiff_subset,
      Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hA)⟩
  · intro A hA
    rw [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hA)]

end Chowla

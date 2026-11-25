import Chowla.Model.Connected
import Chowla.Model.MatchingSum

namespace Chowla

open scoped BigOperators

def widthsOn {ι : Type*} [LinearOrder ι] (a : ι → ℝ) (S : Finset ι) : List ℝ :=
  (S.sort (· ≤ ·)).map a

@[simp] theorem length_widthsOn {ι : Type*} [LinearOrder ι] (a : ι → ℝ) (S : Finset ι) :
    (widthsOn a S).length = S.card := by simp [widthsOn]

@[simp] theorem widthsOn_empty {ι : Type*} [LinearOrder ι] (a : ι → ℝ) :
    widthsOn a ∅ = [] := by simp [widthsOn]

@[simp] theorem widthsOn_singleton {ι : Type*} [LinearOrder ι] (a : ι → ℝ) (i : ι) :
    widthsOn a {i} = [a i] := by simp [widthsOn]

theorem sum_widthsOn {ι : Type*} [LinearOrder ι] (a : ι → ℝ) (S : Finset ι) :
    (widthsOn a S).sum = ∑ i ∈ S, a i := by
  unfold widthsOn
  rw [← List.sum_toFinset a (S.sort_nodup (· ≤ ·))]
  simp

theorem nonneg_mem_widthsOn {ι : Type*} [LinearOrder ι] {a : ι → ℝ} {S : Finset ι}
    (h : ∀ i ∈ S, 0 ≤ a i) : ∀ b ∈ widthsOn a S, 0 ≤ b := by
  intro b hb
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
  exact h i ((Finset.mem_sort (· ≤ ·)).mp hi)

theorem rectangleTail_eq_zero_of_sum {A : List ℝ} (hA : ∀ a ∈ A, 0 ≤ a) (hs : A.sum ≤ 1) :
    rectangleTail A = 0 := by
  simp [rectangleTail, delta_rectangles_eq_zero_of_sum A hA hs]

theorem marked_rectangles_eq_zero_of_sum {h : FourierProfile} (hh : IsProfile h)
    (A : List ℝ) (hA : ∀ a ∈ A, 0 ≤ a) (hlen : 2 ≤ A.length) (hs : radius h + A.sum ≤ 1) :
    cumulant (h :: A.map rectangle) = 0 := by
  rw [cumulant_eq_delta_of_length (by simpa only [List.length_cons, List.length_map] using (Nat.succ_le_succ hlen))]
  apply delta_eq_zero_of_support _ (radius h :: A)
  · intro f hf
    rcases List.mem_cons.mp hf with rfl | he
    · exact hh
    · obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
      exact rectangle_isProfile a
  · refine .cons (hasRadiusAtMost_radius hh) ?_
    clear hlen hs
    induction A with
    | nil => exact .nil
    | cons a A ih =>
      exact .cons (rectangle_hasRadiusAtMost (hA a List.mem_cons_self))
        (ih fun b hb => hA b (List.mem_cons_of_mem a hb))
  · simpa only [List.sum_cons] using hs

theorem rectangleTail_mul_disjoint {ι : Type*} [LinearOrder ι] (a : ι → ℝ)
    (U : Finset ι) (ha : ∀ i ∈ U, 0 ≤ a i) (hU : ∑ i ∈ U, a i ≤ 2)
    {S T : Finset ι} (hS : S ⊆ U) (hT : T ⊆ U) (hdis : Disjoint S T) :
    rectangleTail (widthsOn a S) * rectangleTail (widthsOn a T) = 0 := by
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hS hT) (f := a)
    (fun i hi _ => ha i hi)
  rw [Finset.sum_union hdis] at hsum
  by_cases h : (widthsOn a S).sum ≤ 1
  · rw [rectangleTail_eq_zero_of_sum (nonneg_mem_widthsOn (fun i hi => ha i (hS hi))) h, zero_mul]
  · have ht : (widthsOn a T).sum ≤ 1 := by
      rw [sum_widthsOn] at h ⊢
      linarith
    rw [rectangleTail_eq_zero_of_sum (nonneg_mem_widthsOn (fun i hi => ha i (hT hi))) ht, mul_zero]

theorem marked_rectangles_mul_tail {ι : Type*} [LinearOrder ι] {h : FourierProfile}
    (hh : IsProfile h) (a : ι → ℝ) (U : Finset ι) (ha : ∀ i ∈ U, 0 ≤ a i)
    (hU : radius h + ∑ i ∈ U, a i ≤ 2)
    {S T : Finset ι} (hS : S ⊆ U) (hT : T ⊆ U) (hdis : Disjoint S T) (hSc : 2 ≤ S.card) :
    cumulant (h :: (widthsOn a S).map rectangle) * rectangleTail (widthsOn a T) = 0 := by
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (Finset.union_subset hS hT) (f := a)
    (fun i hi _ => ha i hi)
  rw [Finset.sum_union hdis] at hsum
  by_cases hsmall : (widthsOn a T).sum ≤ 1
  · rw [rectangleTail_eq_zero_of_sum (nonneg_mem_widthsOn (fun i hi => ha i (hT hi))) hsmall, mul_zero]
  · have ht : radius h + (widthsOn a S).sum ≤ 1 := by
      rw [sum_widthsOn] at hsmall ⊢
      linarith
    rw [marked_rectangles_eq_zero_of_sum hh _ (nonneg_mem_widthsOn (fun i hi => ha i (hS hi)))
      (by simpa only [length_widthsOn] using hSc) ht, zero_mul]

theorem sum_marked_rectangles_mul_tail {ι : Type*} [LinearOrder ι] {h : FourierProfile}
    (hh : IsProfile h) (a : ι → ℝ) (U : Finset ι) (ha : ∀ i ∈ U, 0 ≤ a i)
    (hU : radius h + ∑ i ∈ U, a i ≤ 2) (S : Finset ι) (hS : S ⊆ U) :
    (∑ A ∈ S.powerset, cumulant (h :: (widthsOn a A).map rectangle) *
      rectangleTail (widthsOn a (S \ A))) =
      rectangleTail (widthsOn a S) * cumulant [h] +
      ∑ i ∈ S, rectangleTail (widthsOn a (S.erase i)) * cumulant [h, rectangle (a i)] := by
  classical
  let f : Finset ι → ℝ := fun A =>
    cumulant (h :: (widthsOn a A).map rectangle) * rectangleTail (widthsOn a (S \ A))
  have he : (∅ : Finset ι) ∈ S.powerset := Finset.mem_powerset.mpr (Finset.empty_subset _)
  change (∑ A ∈ S.powerset, f A) = _
  rw [← Finset.sum_erase_add S.powerset f he, add_comm]
  have hsub : S.powersetCard 1 ⊆ S.powerset.erase ∅ := by
    intro A hA
    obtain ⟨ha, hc⟩ := Finset.mem_powersetCard.mp hA
    exact Finset.mem_erase.mpr ⟨by intro h; simp [h] at hc, Finset.mem_powerset.mpr ha⟩
  have hsum : (∑ A ∈ S.powerset.erase ∅, f A) = ∑ A ∈ S.powersetCard 1, f A := by
    symm
    apply Finset.sum_subset hsub
    intro A hA hnot
    obtain ⟨hne, hAU⟩ := Finset.mem_erase.mp hA
    have hAS := Finset.mem_powerset.mp hAU
    have hcard : 2 ≤ A.card := by
      have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      have hc : A.card ≠ 1 := fun he => hnot (Finset.mem_powersetCard.mpr ⟨hAS, he⟩)
      omega
    exact marked_rectangles_mul_tail hh a U ha hU (hAS.trans hS)
      (Finset.sdiff_subset.trans hS) disjoint_sdiff_self_right hcard
  rw [hsum, Finset.powersetCard_one, Finset.sum_map]
  congr 1
  · simp [f, mul_comm]
  · apply Finset.sum_congr rfl
    intro i hi
    simp [f, Finset.sdiff_singleton_eq_erase, mul_comm]

end Chowla

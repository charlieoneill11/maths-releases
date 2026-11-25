import Chowla.Claims
import Mathlib.Order.Filter.Finite

namespace Chowla

open Filter
open scoped BigOperators Topology

def discSignOf (d : ℤ) : DiscSign :=
  if d < 0 then .negative else .positive

def discTypeOf (d : ℤ) : DiscType :=
  if d % 4 = 1 then .odd else if d % 8 = 0 then .eight else .four

def discClassOf (d : ℤ) : DiscClass := (discSignOf d, discTypeOf d)

private theorem discSignOf_mul_natAbs (d : ℤ) :
    (discSignOf d).value * (d.natAbs : ℤ) = d := by
  by_cases h : d < 0
  · rw [discSignOf, if_pos h, DiscSign.value, Int.ofNat_natAbs_of_nonpos h.le]
    ring
  · rw [discSignOf, if_neg h, DiscSign.value, Int.natAbs_of_nonneg (le_of_not_gt h), one_mul]

private theorem discSignOf_mul_pos {k d : ℤ} (hk : 0 < k) :
    discSignOf (k * d) = discSignOf d := by
  unfold discSignOf
  have hneg : k * d < 0 ↔ d < 0 := by
    simpa only [mul_zero] using (mul_lt_mul_iff_of_pos_left hk : k * d < k * 0 ↔ d < 0)
  simp only [hneg]

private theorem inClass_discClassOf {d : ℤ} (hd : IsFundDisc d) (hd' : 1 < |d|) :
    InClass (discClassOf d) d := by
  rcases hd with ⟨hd, hsf⟩ | ⟨h4, hmod, hsf⟩
  · have hm : Odd d.natAbs := Int.natAbs_odd.mpr (Int.odd_iff.mpr (by omega))
    have hlt : 1 < d.natAbs := by rw [Int.abs_eq_natAbs] at hd'; exact_mod_cast hd'
    have HT : discTypeOf d = .odd := by simp [discTypeOf, hd]
    unfold discClassOf
    rw [HT]
    refine ⟨d.natAbs, hm, Int.squarefree_natAbs.mpr hsf, ?_, hlt, ?_⟩
    · simp only [DiscType.kappa, Nat.cast_one, one_mul]
      exact (discSignOf_mul_natAbs d).symm
    · rw [discSignOf_mul_natAbs]
      exact hd
  · rcases hmod with hmod | hmod
    · let t := d / 8
      have hd8 : d = 8 * t := by dsimp [t]; omega
      have ht : t % 2 = 1 := by dsimp [t]; omega
      have hsft : Squarefree t := by
        have hdt : d / 4 = 2 * t := by omega
        rw [hdt] at hsf
        exact Squarefree.of_mul_right hsf
      have HT : discTypeOf d = .eight := by unfold discTypeOf; simp [h4, show d % 8 = 0 by omega]
      unfold discClassOf
      rw [HT]
      refine ⟨t.natAbs, Int.natAbs_odd.mpr (Int.odd_iff.mpr ht), Int.squarefree_natAbs.mpr hsft, ?_, trivial⟩
      simp only [DiscType.kappa, Nat.cast_ofNat, mul_assoc]
      rw [hd8, discSignOf_mul_pos (by norm_num : (0 : ℤ) < 8), discSignOf_mul_natAbs]
    · let t := d / 4
      have hd4 : d = 4 * t := by dsimp [t]; omega
      have ht : t % 2 = 1 := by dsimp [t]; omega
      have HT : discTypeOf d = .four := by unfold discTypeOf; simp [h4, show d % 8 ≠ 0 by omega]
      unfold discClassOf
      rw [HT]
      refine ⟨t.natAbs, Int.natAbs_odd.mpr (Int.odd_iff.mpr ht), Int.squarefree_natAbs.mpr hsf, ?_, ?_⟩
      · simp only [DiscType.kappa, Nat.cast_ofNat, mul_assoc]
        rw [hd4, discSignOf_mul_pos (by norm_num : (0 : ℤ) < 4), discSignOf_mul_natAbs]
      · have hS : discSignOf d = discSignOf t := hd4 ▸ discSignOf_mul_pos (by norm_num)
        rw [hS, discSignOf_mul_natAbs]
        exact hmod

theorem discClassOf_eq_of_inClass {D : DiscClass} {d : ℤ} (hd : InClass D d) :
    discClassOf d = D := by
  obtain ⟨m, hm, _, heq, ht⟩ := hd
  have hmpos : 0 < (m : ℤ) := by
    have hn := Nat.odd_iff.mp hm
    omega
  have hK : 0 < (D.2.kappa : ℤ) := by cases D.2 <;> decide
  have hsign : discSignOf d = D.1 := by
    rw [heq, mul_assoc, discSignOf_mul_pos hK]
    generalize D.1 = s
    have hmn : m ≠ 0 := by omega
    cases s <;> simp [DiscSign.value, discSignOf, hmn]
  have htype : discTypeOf d = D.2 := by
    generalize D.2 = t at ht heq ⊢
    cases t with
    | odd =>
      simp only [DiscType.kappa, Nat.cast_one, one_mul] at heq
      have hmod : d % 4 = 1 := by rw [heq]; exact ht.2
      simp [discTypeOf, hmod]
    | four =>
      have hcore : (D.1.value * (m : ℤ)) % 4 = 3 := ht
      have heq' : d = 4 * (D.1.value * (m : ℤ)) := by
        simpa [DiscType.kappa, mul_assoc] using heq
      unfold discTypeOf
      simp [show d % 4 ≠ 1 by omega, show d % 8 ≠ 0 by omega]
    | eight =>
      have heq' : d = 8 * (D.1.value * (m : ℤ)) := by
        simpa [DiscType.kappa, mul_assoc] using heq
      unfold discTypeOf
      simp [show d % 4 ≠ 1 by omega, show d % 8 = 0 by omega]
  exact Prod.ext hsign htype

theorem mem_discs_iff {X : ℝ} {d : ℤ} :
    d ∈ discs X ↔ -⌊X⌋ ≤ d ∧ d ≤ ⌊X⌋ ∧ IsFundDisc d ∧ 1 < |d| := by
  classical
  simp [discs, and_assoc]

theorem mem_classDiscs_iff {D : DiscClass} {X : ℝ} {d : ℤ} :
    d ∈ classDiscs D X ↔ d ∈ discs X ∧ InClass D d := by
  classical
  simp [classDiscs]

theorem classDiscs_eq_filter (D : DiscClass) (X : ℝ) :
    classDiscs D X = (discs X).filter (fun d => discClassOf d = D) := by
  classical
  ext d
  simp only [mem_classDiscs_iff, Finset.mem_filter]
  refine and_congr_right fun hd => ⟨discClassOf_eq_of_inClass, fun h => ?_⟩
  rw [← h]
  have hs := mem_discs_iff.mp hd
  exact inClass_discClassOf hs.2.2.1 hs.2.2.2

/-- The six sign and conductor classes partition the fundamental discriminants. -/
theorem discs_partition (X : ℝ) (d : ℤ) (hd : d ∈ discs X) :
    ∃! D : DiscClass, d ∈ classDiscs D X := by
  refine ⟨discClassOf d, ?_, ?_⟩
  · change d ∈ classDiscs (discClassOf d) X
    rw [classDiscs_eq_filter]
    simp [hd]
  · intro D hD
    rw [classDiscs_eq_filter, Finset.mem_filter] at hD
    exact hD.2.symm

private theorem nonvanishing_classDiscs_eq_filter (D : DiscClass) (X : ℝ) :
    nonvanishing (classDiscs D X) =
      (nonvanishing (discs X)).filter (fun d => discClassOf d = D) := by
  classical
  rw [classDiscs_eq_filter]
  unfold nonvanishing
  ext d
  simp [and_left_comm, and_comm]

private theorem discs_card_eq_sum (X : ℝ) :
    (discs X).card = ∑ D : DiscClass, (classDiscs D X).card := by
  classical
  simp_rw [classDiscs_eq_filter]
  exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)

private theorem nonvanishing_discs_card_eq_sum (X : ℝ) :
    (nonvanishing (discs X)).card =
      ∑ D : DiscClass, (nonvanishing (classDiscs D X)).card := by
  classical
  simp_rw [nonvanishing_classDiscs_eq_filter]
  exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)

/-- An eventual bound in each of the six classes implies the same global statement,
using the smallest of the finitely many rates. -/
theorem mainStatement_of_classStatements (h : ∀ D : DiscClass, ClassStatement D) :
    MainStatement := by
  classical
  choose c hc ht using h
  have hne : (Finset.univ : Finset DiscClass).Nonempty :=
    ⟨(.positive, .odd), Finset.mem_univ _⟩
  let cmin := Finset.univ.inf' hne c
  obtain ⟨D, _, hD⟩ := Finset.exists_mem_eq_inf' hne c
  refine ⟨cmin, ?_, ?_⟩
  · dsimp [cmin]
    rw [hD]
    exact hc D
  · filter_upwards [Filter.eventually_all.mpr ht] with X hX
    rw [discs_card_eq_sum, nonvanishing_discs_card_eq_sum, Nat.cast_sum, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun E _ => ?_
    exact (mul_le_mul_of_nonneg_right (Finset.inf'_le c (Finset.mem_univ E)) (by positivity)).trans (hX E)

end Chowla

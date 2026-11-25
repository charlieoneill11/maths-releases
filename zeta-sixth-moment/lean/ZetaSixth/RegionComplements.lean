import ZetaSixth.LinearBoundaries
import ZetaSixth.RegionGeometry
import Mathlib.Tactic.NormNum

namespace ZetaSixth

open Filter MeasureTheory

private theorem Dacc_cap_ge_two {p : Point} (h : p.2.2 - p.1 ≤ 1 / 2) :
    2 ≤ 3 * min p.1 (1 - p.2.2) + 5 * max p.1 (1 - p.2.2) := by
  rcases le_total p.1 (1 - p.2.2) with horder | horder
  · rw [min_eq_left horder, max_eq_right horder]
    linarith
  · rw [min_eq_right horder, max_eq_left horder]
    linarith

private theorem N0_subset_base_complement : N0 ⊆ Ω \ (S3 ∪ marked) := by
  intro p hp
  obtain ⟨hΩ, hlo, hhi, hk, hspread⟩ := hp
  refine ⟨hΩ, ?_⟩
  rintro ((ha | htrace) | hm)
  · rcases ha.2 with hcap | hshort | hlast
    · exact (not_lt_of_ge (Dacc_cap_ge_two hspread.le)) hcap
    · exact (not_lt_of_ge hk.le) hshort
    · have hx : 0 < p.1 := hΩ.1
      unfold trace shortSum at hhi
      linarith
  · exact htrace.2.elim (not_lt_of_ge hlo.le) (fun h => by linarith)
  · exact (not_lt_of_ge hspread.le) hm.2

private theorem base_complement_pointwise (p : Point)
    (h1 : trace p ≠ 1) (hmid : trace p ≠ 3 / 2) (h2 : trace p ≠ 2)
    (hk : shortSum p ≠ 1 / 2) (hlast : p.2.1 + p.2.2 ≠ 3 / 2)
    (hspread : p.2.2 - p.1 ≠ 1 / 2) :
    p ∈ Ω \ (S3 ∪ marked) ↔ p ∈ N0 ∪ J '' N0 := by
  constructor
  · rintro ⟨hΩ, h⟩
    have hrlo : 1 < trace p := lt_of_le_of_ne
      (le_of_not_gt (fun ht => h (Or.inl (Or.inr ⟨hΩ, Or.inl ht⟩)))) h1.symm
    have hrhi : trace p < 2 := lt_of_le_of_ne
      (le_of_not_gt (fun ht => h (Or.inl (Or.inr ⟨hΩ, Or.inr ht⟩)))) h2
    have hk' : 1 / 2 < shortSum p := lt_of_le_of_ne
      (le_of_not_gt fun ht => h (Or.inl (Or.inl ⟨hΩ, Or.inr (Or.inl ht)⟩))) hk.symm
    have hlast' : p.2.1 + p.2.2 < 3 / 2 := lt_of_le_of_ne
      (le_of_not_gt fun ht => h (Or.inl (Or.inl ⟨hΩ, Or.inr (Or.inr ht)⟩))) hlast
    have hspread' : p.2.2 - p.1 < 1 / 2 := lt_of_le_of_ne
      (le_of_not_gt (fun ht => h (Or.inr ⟨hΩ, ht⟩))) hspread
    rcases lt_or_gt_of_ne hmid with ht | ht
    · exact Or.inl ⟨hΩ, hrlo, ht, hk', hspread'⟩
    · refine Or.inr (mem_J_image.mpr ⟨J_mem_Ω hΩ, ?_, ?_, ?_, ?_⟩)
      · rw [trace_J]
        linarith
      · rw [trace_J]
        linarith
      · rw [shortSum_J]
        linarith
      · rw [spread_J]
        exact hspread'
  · rintro (h | h)
    · exact N0_subset_base_complement h
    · have hJ := N0_subset_base_complement (mem_J_image.mp h)
      refine ⟨J_mem_Ω_iff.mp hJ.1, fun hp => hJ.2 ?_⟩
      apply mem_J_image.mp
      simpa only [Set.image_union, J_S3, J_marked] using hp

/-- The marked complement of Theorem 23, before cutting out the two remaining supports. -/
theorem base_complement_ae : (Ω \ (S3 ∪ marked) : Set Point) =ᵐ[volume] (N0 ∪ J '' N0 : Set Point) := by
  have hk : ∀ᵐ p : Point ∂volume, shortSum p ≠ 1 / 2 := by
    simpa only [shortSum, one_mul, zero_mul, add_zero] using
      ae_ne_coord_level 1 1 0 (1 / 2) (by norm_num)
  have hlast : ∀ᵐ p : Point ∂volume, p.2.1 + p.2.2 ≠ 3 / 2 := by
    simpa only [zero_mul, zero_add, one_mul] using ae_ne_coord_level 0 1 1 (3 / 2) (by norm_num)
  have hspread : ∀ᵐ p : Point ∂volume, p.2.2 - p.1 ≠ 1 / 2 := by
    simpa only [neg_one_mul, zero_mul, add_zero, one_mul, sub_eq_add_neg, add_comm] using
      ae_ne_coord_level (-1) 0 1 (1 / 2) (by norm_num)
  filter_upwards [ae_trace_ne 1, ae_trace_ne (3 / 2), ae_trace_ne 2, hk, hlast, hspread] with p h1 hmid h2 hks hls hsp
  exact propext (base_complement_pointwise p h1 hmid h2 hks hls hsp)

theorem trace_lt_half_of_row {p : Point} (hp : p ∈ balanced ∪ FPlus) :
    trace p < 3 / 2 := by
  rcases hp with hp | hp
  · exact lt_trans hp.2.2.1 (by norm_num)
  · exact hp.2.2.1

private theorem no_reflected_row_on_N0 {p : Point} (hp : p ∈ N0) :
    J p ∉ balanced ∪ FPlus := by
  intro h
  have hlow : trace p < 3 / 2 := hp.2.2.1
  have hhigh := trace_lt_half_of_row h
  rw [trace_J] at hhigh
  linarith

private theorem no_row_on_reflected_N0 {p : Point} (hp : J p ∈ N0) :
    p ∉ balanced ∪ FPlus := by
  simpa only [J_involutive p] using no_reflected_row_on_N0 hp

/-- The two reflected halves of the complement of the mixed-row support. -/
theorem U7_complement_ae :
    (Ω \ U7 : Set Point) =ᵐ[volume]
      ((N0 \ (balanced ∪ FPlus)) ∪ J '' (N0 \ (balanced ∪ FPlus)) : Set Point) := by
  filter_upwards [base_complement_ae] with p hp
  have hbase : (p ∈ Ω ∧ ¬(p ∈ S3 ∨ p ∈ marked)) ↔ (p ∈ N0 ∨ J p ∈ N0) := by
    have hset : (p ∈ Ω \ (S3 ∪ marked)) = (p ∈ N0 ∪ J '' N0) := hp
    simpa only [Set.mem_diff, Set.mem_union, mem_J_image] using (iff_of_eq hset)
  apply propext
  change p ∈ Ω \ U7 ↔ p ∈ (N0 \ (balanced ∪ FPlus)) ∪ J '' (N0 \ (balanced ∪ FPlus))
  have hleft := @no_reflected_row_on_N0 p
  have hright := @no_row_on_reflected_N0 p
  simp only [U7, Set.mem_diff, Set.mem_union, mem_J_image] at hleft hright ⊢
  tauto

/-- The strict inequalities defining the ceiling complement (B) in §10. -/
noncomputable def ceilingLoss : Set Point :=
  Ω ∩ {p | 1 < trace p ∧ trace p < 2 ∧ 1 / 4 < p.1 ∧ p.2.2 < 3 / 4 ∧
    p.2.2 < shortSum p ∧ p.2.1 + p.2.2 - p.1 < 1}

theorem measurableSet_ceilingLoss : MeasurableSet ceilingLoss := by
  change MeasurableSet (Ω ∩ ({p | 1 < p.1 + p.2.1 + p.2.2} ∩
    ({p | p.1 + p.2.1 + p.2.2 < 2} ∩ ({p | 1 / 4 < p.1} ∩ ({p | p.2.2 < 3 / 4} ∩
      ({p | p.2.2 < p.1 + p.2.1} ∩ {p | p.2.1 + p.2.2 - p.1 < 1}))))))
  measurability

private theorem ceiling_complement_pointwise (p : Point)
    (h1 : trace p ≠ 1) (h2 : trace p ≠ 2) (hx : p.1 ≠ 1 / 4) (hz : p.2.2 ≠ 3 / 4)
    (hk : shortSum p ≠ p.2.2) (hs : p.2.1 + p.2.2 - p.1 ≠ 1) :
    p ∈ Ω \ (ceilingBase ∪ J '' ceilingBase) ↔ p ∈ ceilingLoss := by
  constructor
  · rintro ⟨hΩ, hp⟩
    have h1le : 1 ≤ trace p := le_of_not_gt (fun h => hp (Or.inl ⟨hΩ, Or.inr (Or.inl h)⟩))
    have hxle : 1 / 4 ≤ p.1 := le_of_not_gt (fun h => hp (Or.inl ⟨hΩ, Or.inr (Or.inr h)⟩))
    have hkle : p.2.2 ≤ shortSum p := le_of_not_gt (fun h => hp (Or.inl ⟨hΩ, Or.inl h⟩))
    have hJ : J p ∉ ceilingBase := fun h => hp (Or.inr (mem_J_image.mpr h))
    have hJΩ := J_mem_Ω hΩ
    have hJ1 : 1 ≤ trace (J p) := le_of_not_gt (fun h => hJ ⟨hJΩ, Or.inr (Or.inl h)⟩)
    have hJx : 1 / 4 ≤ (J p).1 := le_of_not_gt (fun h => hJ ⟨hJΩ, Or.inr (Or.inr h)⟩)
    have hJk : (J p).2.2 ≤ shortSum (J p) := le_of_not_gt (fun h => hJ ⟨hJΩ, Or.inl h⟩)
    rw [trace_J] at hJ1
    rw [shortSum_J] at hJk
    change 1 / 4 ≤ 1 - p.2.2 at hJx
    change 1 - p.1 ≤ 2 - (p.2.1 + p.2.2) at hJk
    exact ⟨hΩ, lt_of_le_of_ne h1le h1.symm, lt_of_le_of_ne (by linarith) h2,
      lt_of_le_of_ne hxle hx.symm, lt_of_le_of_ne (by linarith) hz,
      lt_of_le_of_ne hkle hk.symm, lt_of_le_of_ne (by linarith) hs⟩
  · rintro ⟨hΩ, hlo, hhi, hsmall, hlarge, hsum, href⟩
    refine ⟨hΩ, ?_⟩
    rintro (h | h)
    · rcases h.2 with h | h | h <;> linarith
    · have hJ := mem_J_image.mp h
      rcases hJ.2 with hJ | hJ | hJ
      · rw [shortSum_J] at hJ
        change 2 - (p.2.1 + p.2.2) < 1 - p.1 at hJ
        linarith
      · rw [trace_J] at hJ
        linarith
      · change 1 - p.2.2 < 1 / 4 at hJ
        linarith

/-- The complement of the first three regions and their reflections, up to null boundaries. -/
theorem ceiling_complement_ae :
    (Ω \ (ceilingBase ∪ J '' ceilingBase) : Set Point) =ᵐ[volume] ceilingLoss := by
  have hx : ∀ᵐ p : Point ∂volume, p.1 ≠ 1 / 4 := by
    simpa only [one_mul, zero_mul, add_zero] using ae_ne_coord_level 1 0 0 (1 / 4) (by norm_num)
  have hz : ∀ᵐ p : Point ∂volume, p.2.2 ≠ 3 / 4 := by
    simpa only [one_mul, zero_mul, zero_add] using ae_ne_coord_level 0 0 1 (3 / 4) (by norm_num)
  have hk : ∀ᵐ p : Point ∂volume, shortSum p ≠ p.2.2 := by
    filter_upwards [ae_ne_coord_level 1 1 (-1) 0 (by norm_num)] with p hp
    unfold shortSum
    intro h
    apply hp
    linarith
  have hs : ∀ᵐ p : Point ∂volume, p.2.1 + p.2.2 - p.1 ≠ 1 := by
    filter_upwards [ae_ne_coord_level (-1) 1 1 1 (by norm_num)] with p hp
    intro h
    apply hp
    linarith
  filter_upwards [ae_trace_ne 1, ae_trace_ne 2, hx, hz, hk, hs] with p h1 h2 hxs hzs hks hss
  exact propext (ceiling_complement_pointwise p h1 h2 hxs hzs hks hss)

theorem J_ceilingLoss : J '' ceilingLoss = ceilingLoss := by
  ext p
  rw [mem_J_image]
  change (J p ∈ Ω ∧ _) ↔ (p ∈ Ω ∧ _)
  rw [J_mem_Ω_iff]
  refine and_congr_right fun _ => ?_
  simp only [Set.mem_setOf_eq, trace_J, shortSum_J]
  change (1 < 3 - trace p ∧ 3 - trace p < 2 ∧ 1 / 4 < 1 - p.2.2 ∧
    1 - p.1 < 3 / 4 ∧ 1 - p.1 < 2 - (p.2.1 + p.2.2) ∧
      (1 - p.2.1) + (1 - p.1) - (1 - p.2.2) < 1) ↔
    (1 < trace p ∧ trace p < 2 ∧ 1 / 4 < p.1 ∧ p.2.2 < 3 / 4 ∧
      p.2.2 < p.1 + p.2.1 ∧ p.2.1 + p.2.2 - p.1 < 1)
  constructor <;> rintro ⟨h1, h2, h3, h4, h5, h6⟩ <;>
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

end ZetaSixth

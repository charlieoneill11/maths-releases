import ZetaSixth.RegionComplements
import ZetaSixth.VolumeCoordinates

namespace ZetaSixth

open Filter MeasureTheory

private theorem mu_absolutelyContinuous : μ ≪ (volume : Measure Point) :=
  (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

private theorem mu_ne_top (s : Set Point) : μ s ≠ ⊤ :=
  ((measure_mono (Set.subset_univ s)).trans_lt mu_finite).ne

private theorem mu_of_complement {s : Set Point} (hm : MeasurableSet s) (hsub : s ⊆ Ω) :
    μ s = μ Ω - μ (Ω \ s) := by
  rw [measure_diff hsub hm.nullMeasurableSet (mu_ne_top s)]
  exact (ENNReal.sub_sub_cancel (mu_ne_top Ω) (measure_mono hsub)).symm

private theorem mu_reflected_pair {s : Set Point} (hm : MeasurableSet s)
    (htrace : ∀ p ∈ s, trace p < 3 / 2) : μ (s ∪ J '' s) = 2 * μ s := by
  have hd : Disjoint s (J '' s) := by
    rw [Set.disjoint_left]
    intro p hp hj
    have hp' := htrace p hp
    have hj' := htrace (J p) (mem_J_image.mp hj)
    rw [trace_J] at hj'
    linarith
  rw [measure_union hd (measurableSet_J_image hm), mu_J_image, two_mul]

theorem mu_U7_from_loss : μ U7 = μ Ω - 2 * μ (N0 \ (balanced ∪ FPlus)) := by
  rw [mu_of_complement measurableSet_U7 U7_subset_Ω,
    measure_congr (mu_absolutelyContinuous.ae_eq U7_complement_ae),
    mu_reflected_pair (measurableSet_N0.diff (measurableSet_balanced.union measurableSet_FPlus))]
  intro p hp
  exact hp.1.2.2.1

private theorem mu_inter_rows (s : Set Point) (hs : MeasurableSet s) :
    μ (s ∩ (balanced ∪ FPlus)) = μ (s ∩ balanced) + μ ((s ∩ FPlus) \ balanced) := by
  have hset : s ∩ (balanced ∪ FPlus) = (s ∩ balanced) ∪ ((s ∩ FPlus) \ balanced) := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_diff]
    tauto
  have hd : Disjoint (s ∩ balanced) ((s ∩ FPlus) \ balanced) := by
    rw [Set.disjoint_left]
    exact fun _ hl hr => hr.2 hl.2
  rw [hset, measure_union hd ((hs.inter measurableSet_FPlus).diff measurableSet_balanced)]

theorem mu_N0_split :
    μ N0 = μ (N0 ∩ balanced) + μ ((N0 ∩ FPlus) \ balanced) + μ (N0 \ (balanced ∪ FPlus)) := by
  have h := measure_diff_add_inter (μ := μ) N0 (measurableSet_balanced.union measurableSet_FPlus)
  rw [mu_inter_rows N0 measurableSet_N0] at h
  exact h.symm.trans (add_comm _ _)

private theorem ceiling_union_rows :
    ceiling =
      (ceilingBase ∪ J '' ceilingBase) ∪ ((balanced ∪ FPlus) ∪ J '' (balanced ∪ FPlus)) := by
  ext p
  simp only [ceiling, Set.image_union, Set.mem_union]
  tauto

private theorem ceiling_subset_Ω : ceiling ⊆ Ω := by
  rw [ceiling_union_rows]
  have hb : ceilingBase ⊆ Ω := Set.inter_subset_left
  have hr : balanced ∪ FPlus ⊆ Ω := Set.union_subset Set.inter_subset_left Set.inter_subset_left
  exact Set.union_subset (Set.union_subset hb (J_image_subset_Ω hb))
    (Set.union_subset hr (J_image_subset_Ω hr))

theorem mu_ceiling_reduction :
    μ ceiling = μ Ω - μ ceilingLoss + 2 * μ (ceilingLoss ∩ balanced) +
      2 * μ ((ceilingLoss ∩ FPlus) \ balanced) := by
  let rows := (balanced ∪ FPlus) ∪ J '' (balanced ∪ FPlus)
  let selected := ceilingLoss ∩ (balanced ∪ FPlus)
  have hselected : MeasurableSet selected :=
    measurableSet_ceilingLoss.inter (measurableSet_balanced.union measurableSet_FPlus)
  have hceiling : ceiling = (ceilingBase ∪ J '' ceilingBase) ∪ rows := ceiling_union_rows
  have hselected_eq : ceilingLoss ∩ rows = selected ∪ J '' selected := by
    dsimp only [rows, selected]
    rw [Set.inter_union_distrib_left, Set.image_inter J_involutive.injective, J_ceilingLoss]
  have h_loss : (Ω \ ceiling : Set Point) =ᵐ[volume] (ceilingLoss \ rows : Set Point) := by
    rw [hceiling]
    filter_upwards [ceiling_complement_ae] with p hp
    apply propext
    change p ∈ Ω \ ((ceilingBase ∪ J '' ceilingBase) ∪ rows) ↔ p ∈ ceilingLoss \ rows
    have hp' : p ∈ Ω \ (ceilingBase ∪ J '' ceilingBase) ↔ p ∈ ceilingLoss := iff_of_eq hp
    simp only [Set.mem_diff, Set.mem_union] at hp' ⊢
    tauto
  have h_gain : μ (ceilingLoss ∩ rows) = 2 * μ selected := by
    rw [hselected_eq, mu_reflected_pair hselected]
    intro p hp
    exact trace_lt_half_of_row hp.2
  have hgain_le : μ (ceilingLoss ∩ rows) ≤ μ ceilingLoss := measure_mono Set.inter_subset_left
  have hB_le : μ ceilingLoss ≤ μ Ω := measure_mono Set.inter_subset_left
  have hfin : (μ ceilingLoss - μ (ceilingLoss ∩ rows)) ≠ ⊤ := ENNReal.sub_ne_top (mu_ne_top ceilingLoss)
  have hr : MeasurableSet rows :=
    (measurableSet_balanced.union measurableSet_FPlus).union
      (measurableSet_J_image (measurableSet_balanced.union measurableSet_FPlus))
  have hdiff : μ (ceilingLoss \ rows) = μ ceilingLoss - μ (ceilingLoss ∩ rows) := by
    have hset : ceilingLoss \ rows = ceilingLoss \ (ceilingLoss ∩ rows) := by
      ext p
      simp only [Set.mem_diff, Set.mem_inter_iff]
      tauto
    rw [hset, measure_diff Set.inter_subset_left (measurableSet_ceilingLoss.inter hr).nullMeasurableSet
      (mu_ne_top (ceilingLoss ∩ rows))]
  rw [mu_of_complement measurableSet_ceiling ceiling_subset_Ω,
    measure_congr (mu_absolutelyContinuous.ae_eq h_loss),
    hdiff,
    (ENNReal.cancel_of_ne hfin).tsub_tsub_assoc hB_le hgain_le, h_gain]
  dsimp only [selected]
  rw [mu_inter_rows ceilingLoss measurableSet_ceilingLoss, mul_add, add_assoc]

theorem mu_ceilingLoss_split :
    μ ceilingLoss = 2 * μ (ceilingLoss ∩ {p | trace p < 3 / 2}) := by
  let lowHalf := ceilingLoss ∩ {p | trace p < 3 / 2}
  have htrace (p : Point) (hp : p ∈ lowHalf) : trace p < 3 / 2 := hp.2
  have hlow : MeasurableSet lowHalf := by
    change MeasurableSet (ceilingLoss ∩ {p : Point | p.1 + p.2.1 + p.2.2 < 3 / 2})
    exact measurableSet_ceilingLoss.inter (by measurability)
  have hpair : ceilingLoss =ᵐ[volume] (lowHalf ∪ J '' lowHalf : Set Point) := by
    filter_upwards [ae_trace_ne (3 / 2)] with p hp
    have hJ : J p ∈ ceilingLoss ↔ p ∈ ceilingLoss := by rw [← mem_J_image, J_ceilingLoss]
    apply propext
    change p ∈ ceilingLoss ↔ p ∈ lowHalf ∪ J '' lowHalf
    simp only [Set.mem_union, mem_J_image, lowHalf, Set.mem_inter_iff, Set.mem_setOf_eq, hJ, trace_J]
    constructor
    · intro h
      rcases lt_or_gt_of_ne hp with ht | ht
      · exact Or.inl ⟨h, ht⟩
      · exact Or.inr ⟨h, by linarith⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  rw [measure_congr (mu_absolutelyContinuous.ae_eq hpair), mu_reflected_pair hlow htrace]

end ZetaSixth

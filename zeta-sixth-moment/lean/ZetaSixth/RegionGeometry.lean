import ZetaSixth.Regions
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace ZetaSixth

open MeasureTheory

theorem continuous_v : Continuous v := by
  unfold v
  fun_prop

theorem continuous_J : Continuous J := by
  unfold J
  fun_prop

theorem J_involutive : Function.Involutive J := by
  intro p
  simp [J]

theorem J_mem_Ω {p : Point} (hp : p ∈ Ω) : J p ∈ Ω := by
  rcases hp with ⟨hx, hxy, hyz, hz⟩
  change 0 < 1 - p.2.2 ∧ 1 - p.2.2 < 1 - p.2.1 ∧
    1 - p.2.1 < 1 - p.1 ∧ 1 - p.1 < 1
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

@[simp]
theorem J_mem_Ω_iff {p : Point} : J p ∈ Ω ↔ p ∈ Ω := by
  refine ⟨fun hp => ?_, J_mem_Ω⟩
  simpa only [J_involutive p] using J_mem_Ω hp

@[simp]
theorem v_comp_J (p : Point) : v (J p) = v p := by
  unfold v J
  ring

theorem shortSum_J (p : Point) : shortSum (J p) = 2 - (p.2.1 + p.2.2) := by
  unfold shortSum J
  ring

theorem lastSum_J (p : Point) : (J p).2.1 + (J p).2.2 = 2 - shortSum p := by
  unfold shortSum J
  ring

theorem trace_J (p : Point) : trace (J p) = 3 - trace p := by
  unfold trace shortSum J
  ring

theorem spread_J (p : Point) : (J p).2.2 - (J p).1 = p.2.2 - p.1 := by
  unfold J
  ring

@[simp]
theorem J_image_image (s : Set Point) : J '' (J '' s) = s := by
  rw [Set.image_image]
  exact (Set.image_congr' (g := id) J_involutive).trans (Set.image_id s)

theorem mem_J_image {s : Set Point} {p : Point} : p ∈ J '' s ↔ J p ∈ s := by
  simp only [J_involutive.image_eq_preimage_symm, Set.mem_preimage]

theorem J_image_subset_Ω {s : Set Point} (hs : s ⊆ Ω) : J '' s ⊆ Ω := by
  rintro p ⟨q, hq, rfl⟩
  exact J_mem_Ω (hs hq)

theorem measurableSet_J_image {s : Set Point} (hs : MeasurableSet s) :
    MeasurableSet (J '' s) := by
  rw [J_involutive.image_eq_preimage_symm]
  exact continuous_J.measurable hs

@[measurability]
theorem measurableSet_Ω : MeasurableSet Ω := by
  change MeasurableSet ({p : Point | 0 < p.1} ∩ ({p | p.1 < p.2.1} ∩
    ({p | p.2.1 < p.2.2} ∩ {p | p.2.2 < 1})))
  measurability

theorem measurableSet_Dacc : MeasurableSet Dacc := by
  change MeasurableSet (Ω ∩ ({p | 3 * min p.1 (1 - p.2.2) + 5 * max p.1 (1 - p.2.2) < 2} ∪
    ({p | p.1 + p.2.1 < 1 / 2} ∪ {p | 3 / 2 < p.2.1 + p.2.2})))
  measurability

theorem measurableSet_A : MeasurableSet A := by
  change MeasurableSet (Ω ∩ ({p | p.1 + p.2.1 + p.2.2 < 1} ∪
    {p | 2 < p.1 + p.2.1 + p.2.2}))
  measurability

theorem measurableSet_marked : MeasurableSet marked := by
  unfold marked
  measurability

theorem measurableSet_N0 : MeasurableSet N0 := by
  change MeasurableSet (Ω ∩ ({p | 1 < p.1 + p.2.1 + p.2.2} ∩
    ({p | p.1 + p.2.1 + p.2.2 < 3 / 2} ∩
      ({p | 1 / 2 < p.1 + p.2.1} ∩ {p | p.2.2 - p.1 < 1 / 2}))))
  measurability

theorem measurableSet_balanced : MeasurableSet balanced := by
  change MeasurableSet (Ω ∩ ({p | 1 < p.1 + p.2.1 + p.2.2} ∩
    ({p | p.1 + p.2.1 + p.2.2 < 15 / 14} ∩
      {p | 21 * (p.1 + p.2.1) + 7 * (p.1 + p.2.1 + p.2.2) < 18})))
  measurability

theorem measurable_xPlus : Measurable xPlus := by
  unfold xPlus
  repeat' apply Measurable.ite
  all_goals measurability

theorem measurableSet_PPlus : MeasurableSet PPlus := by
  have hcap : Measurable (fun a : ℝ × ℝ => xPlus (a.1 + a.2)) :=
    measurable_xPlus.comp (by fun_prop)
  change MeasurableSet ({a : ℝ × ℝ | 0 < a.1} ∩ ({a | a.1 < 1} ∩ ({a | 0 < a.2} ∩
    ({a | a.2 < 1} ∩ ({a | 1 / 2 < a.1 + a.2} ∩ ({a | a.1 + a.2 < 3 / 5} ∩
      {a | a.1 < xPlus (a.1 + a.2)}))))))
  measurability

theorem measurableSet_FPlus : MeasurableSet FPlus := by
  have hpair : Measurable (fun p : Point => (p.1, p.2.1)) := by fun_prop
  have hpre : MeasurableSet ((fun p : Point => (p.1, p.2.1)) ⁻¹' PPlus) :=
    hpair measurableSet_PPlus
  unfold FPlus trace shortSum
  change MeasurableSet
    (Ω ∩ ({p | 1 < p.1 + p.2.1 + p.2.2} ∩ ({p | p.1 + p.2.1 + p.2.2 < 3 / 2} ∩
      ((fun p : Point => (p.1, p.2.1)) ⁻¹' PPlus))))
  measurability

theorem measurableSet_U7 : MeasurableSet U7 := by
  unfold U7 S3
  exact (((((measurableSet_Dacc.union measurableSet_A).union measurableSet_marked).union
    measurableSet_balanced).union (measurableSet_J_image measurableSet_balanced)).union
    measurableSet_FPlus).union (measurableSet_J_image measurableSet_FPlus)

theorem measurableSet_ceilingBase : MeasurableSet ceilingBase := by
  change MeasurableSet (Ω ∩ ({p | p.1 + p.2.1 < p.2.2} ∪
    ({p | p.1 + p.2.1 + p.2.2 < 1} ∪ {p | p.1 < 1 / 4})))
  measurability

theorem measurableSet_ceiling : MeasurableSet ceiling := by
  unfold ceiling
  exact (((((measurableSet_ceilingBase.union
    (measurableSet_J_image measurableSet_ceilingBase)).union measurableSet_balanced).union
    (measurableSet_J_image measurableSet_balanced)).union measurableSet_FPlus).union
    (measurableSet_J_image measurableSet_FPlus))

theorem U7_subset_Ω : U7 ⊆ Ω := by
  have hb : balanced ⊆ Ω := Set.inter_subset_left
  have hf : FPlus ⊆ Ω := Set.inter_subset_left
  unfold U7 S3
  exact Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
    (Set.union_subset (Set.inter_subset_left : Dacc ⊆ Ω) (Set.inter_subset_left : A ⊆ Ω))
    (Set.inter_subset_left : marked ⊆ Ω)) hb) (J_image_subset_Ω hb)) hf) (J_image_subset_Ω hf)

private theorem J_mem_Dacc (p : Point) (hp : p ∈ Dacc) : J p ∈ Dacc := by
  rcases hp with ⟨hΩ, hcap | hfirst | hlast⟩
  · refine ⟨J_mem_Ω hΩ, Or.inl ?_⟩
    simpa [J, min_comm, max_comm] using hcap
  · refine ⟨J_mem_Ω hΩ, Or.inr (Or.inr ?_)⟩
    rw [lastSum_J]
    linarith
  · refine ⟨J_mem_Ω hΩ, Or.inr (Or.inl ?_)⟩
    rw [shortSum_J]
    linarith

private theorem J_mem_A (p : Point) (hp : p ∈ A) : J p ∈ A := by
  rcases hp with ⟨hΩ, hlo | hhi⟩
  · refine ⟨J_mem_Ω hΩ, Or.inr ?_⟩
    rw [trace_J]
    linarith
  · refine ⟨J_mem_Ω hΩ, Or.inl ?_⟩
    rw [trace_J]
    linarith

private theorem J_image_eq_of_mem (s : Set Point) (h : ∀ p ∈ s, J p ∈ s) :
    J '' s = s := by
  ext p
  rw [mem_J_image]
  refine ⟨fun hp => ?_, h p⟩
  simpa only [J_involutive p] using h (J p) hp

theorem J_S3 : J '' S3 = S3 := by
  apply J_image_eq_of_mem
  intro p hp
  exact hp.elim (fun h => Or.inl (J_mem_Dacc p h)) (fun h => Or.inr (J_mem_A p h))

theorem J_marked : J '' marked = marked := by
  apply J_image_eq_of_mem
  intro p hp
  refine ⟨J_mem_Ω hp.1, ?_⟩
  change 1 / 2 < (J p).2.2 - (J p).1
  rw [spread_J]
  exact hp.2

theorem J_U7 : J '' U7 = U7 := by
  simp only [U7, Set.image_union, J_image_image, J_S3, J_marked]
  ext p
  simp only [Set.mem_union]
  tauto

theorem J_ceiling : J '' ceiling = ceiling := by
  simp only [ceiling, Set.image_union, J_image_image]
  ext p
  simp only [Set.mem_union]
  tauto

private theorem Dacc_subset_ceilingBase_union :
    Dacc ⊆ ceilingBase ∪ J '' ceilingBase := by
  intro p hp
  obtain ⟨hΩ, hcap | hfirst | hlast⟩ := hp
  · by_cases hx : p.1 < 1 / 4
    · exact Or.inl ⟨hΩ, Or.inr (Or.inr hx)⟩
    · by_cases hz : 1 - p.2.2 < 1 / 4
      · exact Or.inr (mem_J_image.mpr ⟨J_mem_Ω hΩ, Or.inr (Or.inr hz)⟩)
      · have hmin : (1 : ℝ) / 4 ≤ min p.1 (1 - p.2.2) :=
          le_min (le_of_not_gt hx) (le_of_not_gt hz)
        have hmax : (1 : ℝ) / 4 ≤ max p.1 (1 - p.2.2) :=
          (le_of_not_gt hx).trans (le_max_left _ _)
        exfalso
        linarith
  · have hxy : p.1 < p.2.1 := hΩ.2.1
    have hx : p.1 < 1 / 4 := by unfold shortSum at hfirst; linarith
    exact Or.inl ⟨hΩ, Or.inr (Or.inr hx)⟩
  · have hyz : p.2.1 < p.2.2 := hΩ.2.2.1
    have hz : 1 - p.2.2 < 1 / 4 := by linarith
    exact Or.inr (mem_J_image.mpr ⟨J_mem_Ω hΩ, Or.inr (Or.inr hz)⟩)

private theorem A_subset_ceilingBase_union : A ⊆ ceilingBase ∪ J '' ceilingBase := by
  intro p hp
  obtain ⟨hΩ, hlo | hhi⟩ := hp
  · exact Or.inl ⟨hΩ, Or.inr (Or.inl hlo)⟩
  · have h : trace (J p) < 1 := by rw [trace_J]; linarith
    exact Or.inr (mem_J_image.mpr ⟨J_mem_Ω hΩ, Or.inr (Or.inl h)⟩)

private theorem marked_subset_ceilingBase_union :
    marked ⊆ ceilingBase ∪ J '' ceilingBase := by
  intro p hp
  obtain ⟨hΩ, hspread⟩ := hp
  change 1 / 2 < p.2.2 - p.1 at hspread
  by_cases h : shortSum p < p.2.2
  · exact Or.inl ⟨hΩ, Or.inl h⟩
  · have h' : shortSum (J p) < (J p).2.2 := by
      rw [shortSum_J]
      change 2 - (p.2.1 + p.2.2) < 1 - p.1
      unfold shortSum at h
      linarith [le_of_not_gt h]
    exact Or.inr (mem_J_image.mpr ⟨J_mem_Ω hΩ, Or.inl h'⟩)

theorem U7_subset_ceiling : U7 ⊆ ceiling := by
  intro p hp
  have hS : p ∈ S3 → p ∈ ceilingBase ∪ J '' ceilingBase :=
    fun h => Set.union_subset Dacc_subset_ceilingBase_union A_subset_ceilingBase_union h
  have hZ : p ∈ marked → p ∈ ceilingBase ∪ J '' ceilingBase :=
    fun h => marked_subset_ceilingBase_union h
  simp only [U7, ceiling, Set.mem_union] at hp hS hZ ⊢
  tauto

end ZetaSixth

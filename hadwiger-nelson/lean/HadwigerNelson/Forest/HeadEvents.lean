import HadwigerNelson.Forest.HeadAccounting
import HadwigerNelson.Forest.TwoTails
import HadwigerNelson.Forest.BlankPairs

namespace HadwigerNelson.Forest
open MeasureTheory Set Placement Centres
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

private theorem ae_real_mono {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {s t : Set α} (h : s ≤ᵐ[μ] t) : μ.real s ≤ μ.real t :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae h)

theorem ae_disjoint_of_event {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (h : ∀ᵐ x ∂μ, ¬(x∈s ∧ x∈t)) : AEDisjoint μ s t := by
  rw [ae_iff] at h
  simpa only [not_not,Set.inter_def] using h

/-- A centre event can be added to the finite union of short and unit
events. Only that ordinary union needs to be measurable. -/
theorem head_events_bound {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    [DecidableEq ι] (S B : Finset ι) (h : ι → ℝ) (short centre total : Set α) (E : ι → Set α)
    (c M : ℝ) (hc : 0≤c) (hM : c≤M) (hn : ∀ i∈S,0≤h i)
    (hmS : MeasurableSet short) (hmE : ∀ i∈S,MeasurableSet (E i))
    (hs : c≤μ.real short) (he : ∀ i∈S,h i≤μ.real (E i))
    (exc : ∀ i∈S, i∈B → ∀ j∈S, j∈B → i≠j → AEDisjoint μ (E i) (E j))
    (separate : ∀ᵐ x ∂μ, x∈centre → x∉short ∧ ∀ i∈S,x∉E i)
    (seen : ∀ᵐ x ∂μ, (x∈short ∨ (∃ i∈S,x∈E i) ∨ x∈centre) → x∈total) :
    c + (∑ i∈S,max (h i-M) 0) - (∑ u∈S,∑ v∈S,
      if u≠v ∧ ¬(u∈B ∧ v∈B) then min (h u) (h v) else 0)/2 + μ.real centre ≤ μ.real total := by
  let A := short ∪ ⋃ i∈S,E i
  have mA : MeasurableSet A := hmS.union (S.measurableSet_biUnion hmE)
  have indiv (i) (hi : i∈S) : h i≤μ.real A := (he i hi).trans (measureReal_mono
    (fun _ hi' => Or.inr (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hi'⟩⟩)))
  let T := S.filter (·∈B)
  have ts (i) (hi : i∈T) : i∈S := (Finset.mem_filter.mp hi).1
  have tb (i) (hi : i∈T) : i∈B := (Finset.mem_filter.mp hi).2
  have charge := charged_union S B h (μ.real A) hn indiv (by
    calc ∑ i∈T,h i ≤ ∑ i∈T,μ.real (E i) := Finset.sum_le_sum (fun i hi => he i (ts i hi))
         _ = μ.real (⋃ i∈T,E i) := by
           symm
           exact measureReal_biUnion_finset₀ (fun i hi j hj => exc i (ts i hi) (tb i hi) j (ts j hj) (tb j hj))
             (fun i hi => (hmE i (ts i hi)).nullMeasurableSet)
         _ ≤ μ.real A := by
           refine measureReal_mono ?_ (measure_ne_top _ _)
           intro x hx
           simp only [mem_iUnion] at hx
           obtain ⟨i,hi,hx⟩ := hx
           exact Or.inr (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨ts i hi,hx⟩⟩))
  let ε := (∑ u∈S,∑ v∈S,if u≠v ∧ ¬(u∈B ∧ v∈B) then min (h u) (h v) else 0)/2
  have εpos : 0≤ε := by
    apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg fun u hu => Finset.sum_nonneg fun v hv =>
      by split; exact le_min (hn u hu) (hn v hv); exact le_rfl
  have lower := (head_max_sum S h c M ε hn hc hM εpos).trans
    (max_le (hs.trans (measureReal_mono (subset_union_left (t:=⋃ i∈S,E i)))) charge)
  have apart : AEDisjoint μ A centre := by
    apply ae_disjoint_of_event
    filter_upwards [separate] with x hx
    intro ⟨entry,cen⟩
    have := hx cen
    rcases entry with s | h
    · exact this.1 s
    · simp only [mem_iUnion] at h
      obtain ⟨i,hi,h⟩ := h
      exact this.2 i hi h
  have sub : (A∪centre : Set α) ≤ᵐ[μ] total := by
    filter_upwards [seen] with x hx
    intro h
    apply hx
    rcases h with (hs|hu)|hc
    · exact Or.inl hs
    · obtain ⟨i,hi,hm⟩ := (show ∃ i, ∃ _ : i∈S, x∈E i by simpa only [mem_iUnion] using hu)
      exact Or.inr (Or.inl ⟨i,hi,hm⟩)
    · exact Or.inr (Or.inr hc)
  calc _ ≤ μ.real A + μ.real centre := add_le_add lower le_rfl
       _ = μ.real (A ∪ centre) := (measureReal_union₀' mA.nullMeasurableSet apart).symm
       _ ≤ _ := ae_real_mono sub

end
end HadwigerNelson.Forest

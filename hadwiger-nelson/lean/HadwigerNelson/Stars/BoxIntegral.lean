import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace HadwigerNelson.Stars
open MeasureTheory Set
open scoped Pointwise

/-- A set whose lattice translates are disjoint has its full measure in the
periodised union in a single cell. No choice of representatives on a seam
is needed. -/
theorem periodised_measure {G α : Type*} [AddGroup G] [Countable G] [MeasurableSpace α]
    [AddAction G α] [MeasurableConstVAdd G α] {μ : Measure α} [VAddInvariantMeasure G α μ]
    {C B : Set α} (hc : IsAddFundamentalDomain G C μ) (hC : MeasurableSet C)
    (hB : MeasurableSet B) (disj : Pairwise fun g k : G => Disjoint (g +ᵥ B) (k +ᵥ B)) :
    μ ((⋃ g : G, g +ᵥ B) ∩ C) = μ B := by
  rw [iUnion_inter, hc.measure_eq_tsum B]
  apply measure_iUnion
  · intro g k hne
    exact (disj hne).mono inter_subset_left inter_subset_left
  · intro g
    exact (MeasurableSet.const_vadd hB g).inter hC

/-- Integrate lower bounds on finitely many boxes. Overlaps of measure zero
and pointwise bounds that hold almost everywhere are both allowed. -/
theorem box_integral_lower {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (I : Finset ι) (B : ι → Set α) (c : ι → ℝ) (f : α → ℝ)
    (hm : ∀ i ∈ I, MeasurableSet (B i)) (hf : Integrable f μ)
    (hpos : 0 ≤ᵐ[μ] f)
    (hsep : ∀ᵐ x ∂μ, ∀ i ∈ I, ∀ j ∈ I, x ∈ B i → x ∈ B j → i = j)
    (hlower : ∀ i ∈ I, ∀ᵐ x ∂μ, x ∈ B i → c i ≤ f x) :
    ∑ i ∈ I, μ.real (B i) * c i ≤ ∫ x, f x ∂μ := by
  classical
  let term (i : ι) := (B i).indicator (fun _ => c i)
  have hi (i) (h : i ∈ I) : Integrable (term i) μ :=
    (integrable_const _).indicator (hm i h)
  have hsum : (fun x => ∑ i ∈ I, term i x) ≤ᵐ[μ] f := by
    filter_upwards [hpos, hsep, (Filter.eventually_all_finset I).mpr hlower] with x hp hs hl
    by_cases h : ∃ i ∈ I, x ∈ B i
    · obtain ⟨i, hi, hxi⟩ := h
      rw [Finset.sum_eq_single i]
      · simpa [term, hxi] using hl i hi hxi
      · intro j hj hji
        exact Set.indicator_of_notMem (fun hxj => hji (hs j hj i hi hxj hxi)) _
      · tauto
    · have hz (i) (hi : i ∈ I) : term i x = 0 :=
        Set.indicator_of_notMem (fun hxi => h ⟨i, hi, hxi⟩) _
      rw [Finset.sum_eq_zero hz]
      exact hp
  have h := integral_mono_ae (integrable_finset_sum I hi) hf hsum
  rw [integral_finset_sum I hi] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [term, integral_indicator (hm i hi), setIntegral_const, smul_eq_mul]

/-- Integrate a periodic spatial score using box representatives in the
plane. Their lower estimates may have a null exceptional set. The packing
condition checks disjointness both within a cell and across its boundary. -/
theorem periodised_box_sum {G α ι : Type*} [AddGroup G] [Countable G] [MeasurableSpace α]
    [AddAction G α] [MeasurableConstVAdd G α] {μ : Measure α} [VAddInvariantMeasure G α μ]
    {C : Set α} (hc : IsAddFundamentalDomain G C μ) (hC : MeasurableSet C)
    [IsFiniteMeasure (μ.restrict C)]
    (I : Finset ι) (B : ι → Set α) (c : ι → ℝ) (f : α → ℝ)
    (hB : ∀ i ∈ I, MeasurableSet (B i))
    (pack : ∀ i ∈ I, ∀ j ∈ I, ∀ g h : G, ∀ x, x ∈ g +ᵥ B i → x ∈ h +ᵥ B j → i=j ∧ g=h)
    (period : ∀ g : G, ∀ x, f (g +ᵥ x) = f x) (mf : Measurable f)
    (hf : IntegrableOn f C μ) (hpos : 0 ≤ᵐ[μ.restrict C] f)
    (bounds : ∀ i ∈ I, ∀ᵐ x ∂μ, x ∈ B i → c i ≤ f x) :
    ∑ i ∈ I, μ.real (B i) * c i ≤ ∫ x in C, f x ∂μ := by
  classical
  let good (i : ι) := B i ∩ {x | c i ≤ f x}
  let copies (i : ι) := ⋃ g : G, g +ᵥ good i
  have mg (i) (hi : i ∈ I) : MeasurableSet (good i) :=
    (hB i hi).inter (measurableSet_le measurable_const mf)
  have mc (i) (hi : i ∈ I) : MeasurableSet (copies i) :=
    MeasurableSet.iUnion (fun g : G => MeasurableSet.const_vadd (mg i hi) g)
  have sub (g : G) (i : ι) : g +ᵥ good i ⊆ g +ᵥ B i := by
    rintro x ⟨z,hz,rfl⟩
    exact ⟨z,hz.1,rfl⟩
  have vol (i) (hi : i ∈ I) : (μ.restrict C).real (copies i) = μ.real (B i) := by
    have disj : Pairwise fun g h : G => Disjoint (g +ᵥ good i) (h +ᵥ good i) := by
      intro g h ne
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact ne (pack i hi i hi g h x (sub g i hx) (sub h i hy)).2
    have eq : good i =ᵐ[μ] B i := by
      filter_upwards [bounds i hi] with x hx
      exact propext ⟨And.left, fun h => ⟨h,hx h⟩⟩
    unfold Measure.real
    rw [Measure.restrict_apply (mc i hi), periodised_measure hc hC (mg i hi) disj,
      measure_congr eq]
  have lower := box_integral_lower (μ := μ.restrict C) I copies c f mc hf hpos
    (Filter.Eventually.of_forall (fun x i hi j hj xi xj => by
      obtain ⟨g,hg⟩ := Set.mem_iUnion.mp xi
      obtain ⟨h,hh⟩ := Set.mem_iUnion.mp xj
      exact (pack i hi j hj g h x (sub g i hg) (sub h j hh)).1))
    (fun i _ => Filter.Eventually.of_forall (fun x hx => by
      obtain ⟨g,z,hz,rfl⟩ := Set.mem_iUnion.mp hx
      rw [period]
      exact hz.2))
  simpa only [Finset.sum_congr rfl (fun i hi => congrArg (· * c i) (vol i hi))] using lower

/-- Each of the twelve copies has the same area inside the periodic cell.
The native-box lower bound is per vertex. The Fourier-box bound includes a
factor of one half. The common normalisation is the cell area 6xH. -/
theorem twelve_box_factors (x H d M N : ℝ) (hx : 0 < x) (hH : 0 < H) (hd : 0 < d) :
    (12 * (d/2 * M + d*N) / (6*x*H)) / d = M/(x*H) + 2*N/(x*H) := by
  field_simp
  ring

end HadwigerNelson.Stars

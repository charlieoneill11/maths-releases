import LeastPrime.Cited
import LeastPrime.ProofDefs
import LeastPrime.RevealedDivisors
import Mathlib.MeasureTheory.Measure.Real

/-! Support of the size-biased law on permutations of indexed factors. -/

namespace LeastPrime

open Filter MeasureTheory Real Set
open scoped ENNReal

noncomputable section

theorem weightedMixture_apply {ι Ω : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace Ω]
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (laws : ι → ProbabilityMeasure Ω) (S : Set Ω) :
    (weightedMixture w hw laws : Measure Ω) S =
      ∑ i, ENNReal.ofReal (w i / ∑ k, w k) * ((laws i : Measure Ω) S) := by
  simp [weightedMixture, Measure.finset_sum_apply]

private def weightVector (logN : ℝ) (j : ℕ) (weights : List {w : ℝ // 0 < w}) :
    Fin j → ℝ :=
  fun i => ((weights[i.val]?.map Subtype.val).getD 0) / logN

private theorem weightVector_cons (logN : ℝ) (j : ℕ) (a : {w : ℝ // 0 < w})
    (weights : List {w : ℝ // 0 < w}) :
    weightVector logN (j + 1) (a :: weights) =
      Fin.cons (a.val / logN) (weightVector logN j weights) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [weightVector]
  | succ i => simp [weightVector]

private theorem sizeBiasedFromLogs_full_of_perm {α : Type*} (w : α → {w : ℝ // 0 < w})
    (logN : ℝ) (j : ℕ) (factors : List α) {A : Set (Fin j → ℝ)} (hA : MeasurableSet A)
    (hperm : ∀ ordered : List α, ordered.Perm factors →
      weightVector logN j (ordered.map w) ∈ A) :
    (sizeBiasedFromLogs logN j (factors.map w) : Measure (Fin j → ℝ)) A = 1 := by
  induction j generalizing factors with
  | zero =>
    have hz : weightVector logN 0 (factors.map w) = 0 := funext (fun i => i.elim0)
    rw [sizeBiasedFromLogs, ProbabilityMeasure.coe_mk, Measure.dirac_apply_of_mem]
    simpa [hz] using hperm factors (.refl _)
  | succ j ih =>
    cases factors with
    | nil =>
      have hz : weightVector logN (j + 1) [] = 0 := by ext i; simp [weightVector]
      rw [List.map_nil, sizeBiasedFromLogs, ProbabilityMeasure.coe_mk, Measure.dirac_apply_of_mem]
      simpa [hz] using hperm [] (.refl _)
    | cons first rest =>
      let factors := first :: rest
      let keys := factors.map w
      have hall (i : Fin (rest.length + 1)) (hi' : i.val < keys.length) :
          ((sizeBiasedFromLogs logN j (keys.eraseIdx i.val) : Measure (Fin j → ℝ))
            ((Fin.cons (α := fun _ : Fin (j + 1) => ℝ) (keys[i.val].val / logN)) ⁻¹' A)) = 1 := by
        have hi : i.val < factors.length := i.isLt
        have hkey : keys[i.val] = w factors[i.val] := by simp [keys]
        let c : (Fin j → ℝ) → (Fin (j + 1) → ℝ) :=
          Fin.cons (α := fun _ : Fin (j + 1) => ℝ) (keys[i.val].val / logN)
        have hm : Measurable c := by
          apply measurable_pi_lambda
          intro k
          cases k using Fin.cases with
          | zero => simp [c]
          | succ k => simpa [c] using (measurable_pi_apply k :
              Measurable (fun x : (Fin j → ℝ) => x k))
        change (sizeBiasedFromLogs logN j (keys.eraseIdx i.val) : Measure (Fin j → ℝ))
          (c ⁻¹' A) = 1
        rw [show keys.eraseIdx i.val = (factors.eraseIdx i.val).map w from List.eraseIdx_map _ _ _]
        apply ih (factors.eraseIdx i.val) (hA.preimage hm)
        intro ordered hp
        have hOrdered : (factors[i.val] :: ordered).Perm factors :=
          (hp.cons _).trans (List.getElem_cons_eraseIdx_perm hi)
        have h := hperm (factors[i.val] :: ordered) hOrdered
        simpa [c, hkey, weightVector_cons] using h
      rw [List.map_cons, sizeBiasedFromLogs, weightedMixture_apply]
      conv_rhs =>
        rw [← measure_univ (μ :=
            (sizeBiasedFromLogs logN (j + 1) (w first :: rest.map w) :
              Measure (Fin (j + 1) → ℝ))),
          sizeBiasedFromLogs, weightedMixture_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [measure_univ, ProbabilityMeasure.map_apply' _ _ hA]
      exact hall ⟨i.val, by simpa using i.isLt⟩ (by simpa [keys, factors] using i.isLt)

private theorem weightVector_eq_revealed {α : Type*} (n j : ℕ) (w : α → {w : ℝ // 0 < w})
    (f : α → ℕ) (hw : ∀ a, (w a : ℝ) = log (f a : ℝ)) (l : List α) :
    weightVector (log n) j (l.map w) = revealedVector j n (l.map f) := by
  funext i
  simp only [weightVector, revealedVector, List.getElem?_map, Option.map_map]
  cases hi : l[i.val]? <;> simp [Function.comp_def, hw]

/-- A measurable event containing every prime-factor ordering has full size-biased probability. -/
theorem sizeBiasedLaw_full_of_perm (j n : ℕ) {A : Set (Fin j → ℝ)} (hA : MeasurableSet A)
    (hperm : ∀ factors : List ℕ, factors.Perm n.primeFactorsList →
      revealedVector j n factors ∈ A) :
    (sizeBiasedLaw j n : Measure (Fin j → ℝ)) A = 1 := by
  unfold sizeBiasedLaw primeLogs
  apply sizeBiasedFromLogs_full_of_perm _ _ _ _ hA
  intro l hl
  rw [weightVector_eq_revealed n j _ Subtype.val (fun _ => rfl)]
  apply hperm
  have h := hl.map Subtype.val
  rw [List.attach_map_subtype_val] at h
  exact h.trans n.primeFactorsList.reverse_perm

open Classical in
/-- A revealed witness for the inner event implies a divisor witness. -/
theorem sizeBiasedLaw_real_E_le_indicator {j n : ℕ} (hn : 2 ≤ n)
    {T : Set ℝ} (hE : MeasurableSet (E j T)) :
    (sizeBiasedLaw j n : Measure (Fin j → ℝ)).real (E j T) ≤
      (if HasLogDivisorIn n T then 1 else 0 : ℝ) := by
  classical
  by_cases h : HasLogDivisorIn n T
  · rw [if_pos h]
    exact
      (measureReal_mono (μ := (sizeBiasedLaw j n : Measure (Fin j → ℝ)))
        (Set.subset_univ (E j T))).trans_eq probReal_univ
  · rw [if_neg h]
    have hfull := sizeBiasedLaw_full_of_perm j n hE.compl (fun factors hp hm =>
      h (divisor_of_revealed hn hp hm))
    have hreal : (sizeBiasedLaw j n : Measure (Fin j → ℝ)).real (E j T)ᶜ = 1 := by
      rw [measureReal_def, hfull, ENNReal.toReal_one]
    rw [probReal_compl_eq_one_sub hE] at hreal
    linarith

open Classical in
/-- A divisor witness entails membership in the outer event for every ordering. -/
theorem indicator_le_sizeBiasedLaw_real_F {j n : ℕ} (hn : 2 ≤ n)
    {T : Set ℝ} (hF : MeasurableSet (F j T)) :
    (if HasLogDivisorIn n T then 1 else 0 : ℝ) ≤
      (sizeBiasedLaw j n : Measure (Fin j → ℝ)).real (F j T) := by
  classical
  by_cases h : HasLogDivisorIn n T
  · rw [if_pos h, measureReal_def,
      sizeBiasedLaw_full_of_perm j n hF (fun _ hp => revealed_of_divisor hn hp h),
      ENNReal.toReal_one]
  · rw [if_neg h]
    exact measureReal_nonneg

end

end LeastPrime

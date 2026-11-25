import HadwigerNelson.Stars.Expectation

namespace HadwigerNelson.Stars
open MeasureTheory Set

variable {V Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- A statistic of finitely many colours is integrable on a finite measure
space as soon as each individual colouring event is measurable. -/
theorem integrable_statistic (S : Finset V) (κ : Ω → V → Option (Fin 6))
    (f : (V → Option (Fin 6)) → ℝ)
    (locality : ∀ a b, (∀ v ∈ S, a v = b v) → f a = f b)
    (hm : ∀ v ∈ S, ∀ k, MeasurableSet {ω | κ ω v = k}) :
    Integrable (fun ω => f (κ ω)) μ := by
  classical
  let extend (w : S → Option (Fin 6)) (v : V) := if h : v ∈ S then w ⟨v,h⟩ else none
  let event (w : S → Option (Fin 6)) := {ω | ∀ v : S, κ ω v = w v}
  have meas (w : S → Option (Fin 6)) : MeasurableSet (event w) := by
    change MeasurableSet {ω | ∀ v : S, κ ω v = w v}
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun v : S => hm v v.2 (w v))
  have expansion (ω : Ω) : f (κ ω) =
      ∑ w : S → Option (Fin 6), (event w).indicator (fun _ => f (extend w)) ω := by
    let w₀ (v : S) := κ ω v
    rw [Finset.sum_eq_single w₀]
    · rw [Set.indicator_of_mem (show ω ∈ event w₀ from fun _ => rfl)]
      exact locality _ _ (fun v hv => by simp [extend, hv, w₀])
    · intro w _ hne
      apply Set.indicator_of_notMem
      exact fun hw => hne (funext (fun v => (hw v).symm))
    · simp
  simp_rw [expansion]
  exact integrable_finset_sum _ (fun w _ => (integrable_const _).indicator (meas w))

/-- The gain at a vertex depends only on its colour and the colours at listed endpoints. -/
theorem gain_congr (S : Finset V) (E : Finset (V × V)) (v : V) (hv : v ∈ S)
    (ends : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S) (a b : V → Option (Fin 6))
    (agree : ∀ x ∈ S, a x = b x) : gain E a v = gain E b v := by
  classical
  have hb : badEdges E a = badEdges E b := by
    apply Finset.filter_congr
    intro e he
    simp [Bad, agree _ (ends e he).1, agree _ (ends e he).2]
  have hs (k : Fin 6) : Sees E a v k ↔ Sees E b v k := by
    unfold Sees
    apply exists_congr
    intro e
    apply and_congr_right
    intro he
    rw [agree _ (ends e he).1, agree _ (ends e he).2]
  have hl : Locked E a v ↔ Locked E b v := by
    unfold Locked
    simp only [agree v hv, hs]
  simp only [gain, sameCount, hb, locked, hl]

theorem integrable_gain (S : Finset V) (E : Finset (V × V)) (v : V) (hv : v ∈ S)
    (ends : ∀ e ∈ E, e.1 ∈ S ∧ e.2 ∈ S) (κ : Ω → V → Option (Fin 6))
    (hm : ∀ x ∈ S, ∀ k, MeasurableSet {ω | κ ω x = k}) :
    Integrable (fun ω => gain E (κ ω) v) μ :=
  integrable_statistic S κ (fun c => gain E c v) (gain_congr S E v hv ends) hm

end HadwigerNelson.Stars

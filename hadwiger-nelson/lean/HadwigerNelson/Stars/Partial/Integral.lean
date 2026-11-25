import HadwigerNelson.Stars.Partial.Step
import HadwigerNelson.Stars.Partial.Tree

/-! Exact integrals of the common lower step against a continuous test function.
The test functions used by the checker are one and the positive Fourier characters. -/

namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (Span endpoint resolution spanEval changeOf)
open MeasureTheory Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def primitive (f : ℝ → E) (q : Nat) (c _ : Int) (i : Nat) : E :=
  (c:ℝ) • ∫ θ in 0..endpoint q i, f θ

private theorem integral_congr_interior {a b : ℝ} (ab : a≤b) {f g : ℝ → E}
    (eq : ∀ x∈Ioo a b, f x=g x) :
    (∫ x in a..b, f x) = ∫ x in a..b, g x := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume b] with t ht mem
  rw [uIoc_of_le ab] at mem
  exact eq t ⟨mem.1,lt_of_le_of_ne mem.2 ht⟩

private theorem leaf_integrable (src : Angular.Box) (other q d a : Nat) (f : ℝ → E)
    (hf : Continuous f) (l u : ℝ) :
    IntervalIntegrable (fun t => leafValue src other q d a t • f t) volume l u := by
  have hi : IntervalIntegrable (leafValue src other q d a) volume l u :=
    intervalIntegrable_iff.mpr (Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (leaf_measurable ..).aestronglyMeasurable (Filter.Eventually.of_forall (leaf_norm src other q d a)))
  exact hi.smul_continuousOn hf.continuousOn

private theorem const_eq (f : ℝ → E) (hf : Continuous f) (q a b : Nat) (c : Int) :
    (∫ t in endpoint q a..endpoint q b, (c:ℝ) • f t) =
      changeOf (primitive f) ⟨q,a,b,c,0⟩ := by
  simp only [changeOf,primitive,intervalIntegral.integral_smul,←smul_sub]
  congr 1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 (endpoint q a)) (hf.intervalIntegrable _ (endpoint q b))]
  abel

theorem leaf_integral (src : Angular.Box) (other q d a : Nat) (f : ℝ → E) (hf : Continuous f) :
    (∫ θ in endpoint q a..endpoint q (a+2^d), leafValue src other q d a θ • f θ) =
      treeEval src other q (changeOf (primitive f)) d a := by
  induction d generalizing a with
  | zero => exact const_eq f hf q a _ _
  | succ d ih =>
    have splitEnd : a+2^d+2^d = a+2^(d+1) := by rw [pow_succ];omega
    by_cases fixed : (node src other q a (a+2^(d+1))).2
    · simp only [leafValue,treeEval,fixed,if_true]
      exact const_eq f hf q a _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals (b:=endpoint q (a+2^d))
      (leaf_integrable src other q (d+1) a f hf _ _) (leaf_integrable src other q (d+1) a f hf _ _)]
    simp only [treeEval,fixed,Bool.false_eq_true,if_false]
    congr 1
    · rw [←ih]
      apply integral_congr_interior (BoxCheck.endpoint_monotone q (Nat.le_add_right ..))
      intro θ ht
      simp only [leafValue,fixed,Bool.false_eq_true,if_false,if_pos ht.2]
    · rw [←ih (a+2^d),splitEnd]
      have cmp : a+2^d ≤ a+2^(d+1) := splitEnd ▸ Nat.le_add_right _ _
      apply integral_congr_interior (BoxCheck.endpoint_monotone q cmp)
      intro θ ht
      simp only [leafValue,fixed,Bool.false_eq_true,if_false,if_neg (not_lt_of_ge ht.1.le)]

theorem witness_integrable (src : Angular.Box) (other : Nat) (a b : ℝ) :
    IntervalIntegrable (witness src other) volume a b :=
  intervalIntegrable_iff.mpr (Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
    (witness_measurable ..).aestronglyMeasurable (Filter.Eventually.of_forall (witness_norm src other)))

theorem witness_integral (src : Angular.Box) (other : Nat) (f : ℝ → E) (hf : Continuous f) :
    (∫ θ in 0..2*Real.pi, witness src other θ • f θ) =
      spanEval (runs src other) (changeOf (primitive f)) := by
  let g (θ : ℝ) := witness src other θ • f θ
  have gi (a b : ℝ) : IntervalIntegrable g volume a b :=
    (witness_integrable src other a b).smul_continuousOn hf.continuousOn
  have piece (q : Nat) (hq : q<4) :
      (∫ θ in endpoint q 0..endpoint q resolution, g θ) =
        treeEval src other q (changeOf (primitive f)) 17 0 := by
    rw [←leaf_integral src other q 17 0 f hf]
    apply integral_congr_interior (BoxCheck.endpoint_monotone q (Nat.zero_le _))
    intro θ ht
    have eq := quarter_of_mem hq ⟨ht.1.le,ht.2⟩
    have a : 0≤endpoint q 0 := by simp [endpoint,BoxCheck.paramAngle];positivity
    have b : endpoint q resolution ≤ 2*Real.pi := by
      rw [BoxCheck.endpoint_edge]
      simp [endpoint,BoxCheck.paramAngle]
      have q' : ((q+1:Nat):ℝ) ≤ 4 := by exact_mod_cast hq
      push_cast at q'
      nlinarith [mul_nonneg (sub_nonneg.mpr q') Real.pi_pos.le]
    dsimp only [g,witness,turnValue]
    rw [wrap_id ⟨a.trans ht.1.le,ht.2.trans_le b⟩,eq]
  rw [runs_eval _ _ _ (by intros;simp [primitive])]
  rw [←piece 0 (by decide),←piece 1 (by decide),←piece 2 (by decide),←piece 3 (by decide)]
  rw [BoxCheck.endpoint_edge 0,BoxCheck.endpoint_edge 1,BoxCheck.endpoint_edge 2,
    BoxCheck.endpoint_full,BoxCheck.endpoint_zero]
  exact (by
    rw [intervalIntegral.integral_add_adjacent_intervals (gi ..) (gi ..),
      intervalIntegral.integral_add_adjacent_intervals (gi ..) (gi ..),
      intervalIntegral.integral_add_adjacent_intervals (gi ..) (gi ..)])

end
end HadwigerNelson.Stars.PartialCheck

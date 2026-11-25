import HadwigerNelson.Stars.Partial.Colour
import Mathlib.MeasureTheory.Function.Floor

/-! A common measurable periodic lower function for every centre of a given source.
A half-open convention assigns each subdivision seam to a unique bin. -/
namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (endpoint resolution)
open Set MeasureTheory
noncomputable section

def wrap (θ : ℝ) : ℝ := θ-(⌊θ/(2*Real.pi)⌋:ℤ)*(2*Real.pi)

theorem wrap_mem (θ : ℝ) : wrap θ ∈ Ico 0 (2*Real.pi) := by
  have p : 0<(2*Real.pi) := by positivity
  have lo := (le_div_iff₀ p).mp (Int.floor_le (θ/(2*Real.pi)))
  have hi := (div_lt_iff₀ p).mp (Int.lt_floor_add_one (θ/(2*Real.pi)))
  unfold wrap
  constructor <;> linarith

theorem wrap_id {θ : ℝ} (h : θ ∈ Ico 0 (2*Real.pi)) : wrap θ=θ := by
  unfold wrap
  have p : 0<(2*Real.pi) := by positivity
  rw [Int.floor_eq_zero_iff.mpr ⟨div_nonneg h.1 p.le,(div_lt_one p).mpr h.2⟩]
  norm_num

theorem wrap_period : Function.Periodic wrap (2*Real.pi) := by
  intro θ
  unfold wrap
  rw [add_div,div_self (by positivity : 2*Real.pi ≠ 0),Int.floor_add_one]
  push_cast
  ring

theorem wrap_measurable : Measurable wrap := by
  unfold wrap
  fun_prop

def leafValue (src : Angular.Box) (other q : Nat) : Nat → Nat → ℝ → ℝ
  | 0,a,_ => (node src other q a (a+1)).1
  | d+1,a,t =>
    let p := node src other q a (a+2^(d+1))
    if p.2 then p.1 else
    if t<endpoint q (a+2^d) then leafValue src other q d a t
    else leafValue src other q d (a+2^d) t

theorem leaf_measurable (src : Angular.Box) (other q d a : Nat) :
    Measurable (leafValue src other q d a) := by
  induction d generalizing a with
  | zero => exact measurable_const
  | succ d ih =>
    change Measurable (fun t => leafValue src other q (d+1) a t)
    by_cases fixed : (node src other q a (a+2^(d+1))).2
    · simp only [leafValue,fixed,if_true]; exact measurable_const
    · simp only [leafValue,fixed,Bool.false_eq_true,if_false]
      exact (ih a).ite measurableSet_Iio (ih _)

theorem leaf_norm (src : Angular.Box) (other q d a : Nat) (θ : ℝ) :
    ‖leafValue src other q d a θ‖ ≤ 1 := by
  have sign (i j : Nat) : ‖((node src other q i j).1:ℝ)‖ ≤ 1 := by
    have bound (n a : BoxCheck.Status) : -1 ≤ (lowerStep n a).1 ∧ (lowerStep n a).1 ≤ 1 := by
      cases n <;> cases a <;> decide
    have both : -1 ≤ (node src other q i j).1 ∧ (node src other q i j).1 ≤ 1 := bound _ _
    exact abs_le.mpr (by exact_mod_cast both)
  induction d generalizing a with
  | zero => exact sign _ _
  | succ d ih =>
    by_cases fixed : (node src other q a (a+2^(d+1))).2
    · simp only [leafValue,fixed,if_true]; exact sign _ _
    · simp only [leafValue,fixed,Bool.false_eq_true,if_false]
      split <;> exact ih _

theorem leaf_lower (src : Angular.Box) (other : Nat)
    (legal : other=0 ∨ (1≤other ∧ other≤6 ∧ BoxCheck.actualLabel 1 ≠ BoxCheck.actualLabel other))
    (z : Plane) (inside : BoxCheck.InBox src (10^12*z 0) (10^12*z 1)) (xrange : 0≤z 0 ∧ z 0≤1)
    (q : Nat) (hq : q<4) (d a : Nat) (stop : a+2^d≤resolution) (θ : ℝ)
    (ht : θ∈Ico (endpoint q a) (endpoint q (a+2^d))) :
    leafValue src other q d a θ ≤ response z other θ := by
  induction d generalizing a with
  | zero => exact node_lower src other legal z inside xrange hq (Nat.le_add_right ..) stop ⟨ht.1,ht.2.le⟩
  | succ d ih =>
    have hsplit : a+2^d+2^d = a+2^(d+1) := by rw [pow_succ];omega
    by_cases fixed : (node src other q a (a+2^(d+1))).2
    · simp only [leafValue,fixed,if_true]
      exact node_lower src other legal z inside xrange hq (Nat.le_add_right ..) stop ⟨ht.1,ht.2.le⟩
    · simp only [leafValue,fixed,Bool.false_eq_true,if_false]
      split
      · rename_i h
        exact ih a ((Nat.le_add_right (a+2^d) (2^d)).trans (hsplit ▸ stop)) ⟨ht.1,h⟩
      · rename_i h
        exact ih (a+2^d) (hsplit ▸ stop) ⟨le_of_not_gt h,hsplit.symm ▸ ht.2⟩

def quarter (θ : ℝ) : Nat :=
  if θ<Real.pi/2 then 0 else if θ<Real.pi then 1 else if θ<3*(Real.pi/2) then 2 else 3

theorem quarter_lt (θ : ℝ) : quarter θ<4 := by unfold quarter; split_ifs <;> decide

theorem quarter_mem {θ : ℝ} (h : θ∈Ico 0 (2*Real.pi)) :
    θ∈Ico (endpoint (quarter θ) 0) (endpoint (quarter θ) resolution) := by
  have seam (q : Nat) : endpoint q 0=(q:ℝ)*(Real.pi/2) := by simp [endpoint,BoxCheck.paramAngle]
  rw [BoxCheck.endpoint_edge,seam,seam]
  unfold quarter
  split_ifs <;> constructor <;> norm_num <;> linarith [h.1,h.2,Real.pi_pos]

theorem quarter_of_mem {θ : ℝ} {q : Nat} (hq : q<4)
    (h : θ∈Ico (endpoint q 0) (endpoint q resolution)) : quarter θ=q := by
  have seam (q : Nat) : endpoint q 0=(q:ℝ)*(Real.pi/2) := by simp [endpoint,BoxCheck.paramAngle]
  rw [BoxCheck.endpoint_edge,seam,seam] at h
  obtain ⟨l,u⟩ := h
  interval_cases q <;> norm_num at l u <;> unfold quarter <;> repeat first | split | rfl | linarith [Real.pi_pos]

def turnValue (src : Angular.Box) (other : Nat) (θ : ℝ) : ℝ :=
  leafValue src other (quarter θ) 17 0 θ

def witness (src : Angular.Box) (other : Nat) (θ : ℝ) : ℝ := turnValue src other (wrap θ)

theorem witness_period (src : Angular.Box) (other : Nat) :
    Function.Periodic (witness src other) (2*Real.pi) :=
  fun θ => congrArg (turnValue src other) (wrap_period θ)

theorem witness_norm (src : Angular.Box) (other : Nat) (θ : ℝ) : ‖witness src other θ‖ ≤ 1 :=
  leaf_norm ..

theorem witness_measurable (src : Angular.Box) (other : Nat) : Measurable (witness src other) := by
  apply Measurable.comp (g := turnValue src other) _ wrap_measurable
  let l (q : Nat) := leafValue src other q 17 0
  have id : turnValue src other = fun θ =>
      if θ<Real.pi/2 then l 0 θ else if θ<Real.pi then l 1 θ else if θ<3*(Real.pi/2) then l 2 θ else l 3 θ := by
    funext θ
    unfold turnValue quarter
    repeat first | split | rfl
  rw [id]
  exact (leaf_measurable ..).ite measurableSet_Iio
    ((leaf_measurable ..).ite measurableSet_Iio ((leaf_measurable ..).ite measurableSet_Iio (leaf_measurable ..)))

theorem witness_lower (src : Angular.Box) (other : Nat)
    (legal : other=0 ∨ (1≤other ∧ other≤6 ∧ BoxCheck.actualLabel 1 ≠ BoxCheck.actualLabel other))
    (z : Plane) (inside : BoxCheck.InBox src (10^12*z 0) (10^12*z 1)) (xrange : 0≤z 0 ∧ z 0≤1)
    (θ : ℝ) : witness src other θ ≤ response z other θ := by
  have per : Function.Periodic (response z other) (2*Real.pi) := by
    by_cases h : other=0
    · simpa [response,h] using colourResponse_period PartialWave.datum z (BoxCheck.actualLabel 1)
    · simpa [response,h] using (colourResponse_period PartialWave.datum z (BoxCheck.actualLabel 1)).sub
        (colourResponse_period PartialWave.datum z (BoxCheck.actualLabel other))
  have h := leaf_lower src other legal z inside xrange _ (quarter_lt (wrap θ)) 17 0
    (by decide) (wrap θ) (quarter_mem (wrap_mem θ))
  exact h.trans_eq (per.sub_int_mul_eq _)

end
end HadwigerNelson.Stars.PartialCheck

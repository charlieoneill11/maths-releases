import HadwigerNelson.Stars.CreditRuntime
import HadwigerNelson.Stars.Threshold
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Interpretation of each finite integer comparison in the real-valued
native, signed-harmonic, and Fejér bounds. -/

namespace HadwigerNelson.Stars.BoxCheck
open scoped BigOperators

theorem array_sum_ofFn {n : Nat} (f : Fin n → Int) :
    (Array.ofFn f).sum = ∑ i, f i := by
  rw [← Array.sum_toList,Array.toList_ofFn,List.sum_ofFn]

theorem array_all_ofFn {n : Nat} (f : Fin n → Bool) :
    (Array.ofFn f).all id = true ↔ ∀ i, f i = true := by
  rw [Array.all_eq_true]
  simp only [Array.getElem_ofFn,Array.size_ofFn,id_eq]
  exact ⟨fun h i => h i.val i.isLt, fun h i hi => h ⟨i,hi⟩⟩

private theorem list_sum_by {α : Type*} (f : α → Int) (xs : List α) (z : Int) :
    xs.foldl (fun a x => a+f x) z = z+(xs.map f).sum := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih => simp [ih,add_assoc]

theorem array_sum_by {α : Type*} (f : α → Int) (xs : Array α) :
    xs.foldl (fun a x => a+f x) 0 = ∑ i : Fin xs.size, f xs[i.val] := by
  rw [← Array.foldl_toList, list_sum_by,zero_add]
  conv_lhs => rw [← List.ofFn_getElem (xs := xs.toList)]
  simp [List.map_ofFn,List.sum_ofFn]

theorem fejerSum_eq (ts : Array Int) :
    fejerSum ts = ∑ i : Fin harmonics,
      2*((harmonics : Int)-i.val)*(ts[i.val]?.getD 0)*(ts[i.val]?.getD 0) :=
  array_sum_ofFn _

/-- The native and harmonic estimates, with all profile and Fourier scales restored. -/
theorem targetPass_sound (d : Nat) (hd : 0 < d) (nat score : Int)
    (pass : targetPass d nat score = true) :
    (8 : ℝ)/10^9 ≤ nat/((CompleteWave.xInt : ℝ)*quant*d) +
      2*score/((CompleteWave.xInt : ℝ)*quant*thresholdScale) := by
  have p : (8 : Int)*CompleteWave.xInt*quant*thresholdScale*d ≤
      (nat*thresholdScale+2*score*d)*10^9 := of_decide_eq_true pass
  have r : (8 : ℝ)*CompleteWave.xInt*quant*thresholdScale*d ≤
      (nat*thresholdScale+2*score*d)*10^9 := by exact_mod_cast p
  have hr : (0 : ℝ) < d := by exact_mod_cast hd
  norm_num [CompleteWave.xInt,quant,thresholdScale] at r ⊢
  field_simp [hr.ne']
  linarith

/-- The integer weighted sum is exactly the Fejér sum in Lemma 24. -/
theorem fejerPass_sound (d : Nat) (hd : 0 < d) (ts : Array Int)
    (pass : fejerPass d ts = true) :
    (∑ k : Fin harmonics,
      fejerWeight harmonics k * (((ts[k.val]?.getD 0 : Int) : ℝ)/thresholdScale)^2) <
      ((harmonics : ℝ)+1)/d-1 := by
  have pos : (0 : ℝ) < d := by exact_mod_cast hd
  have u : (d : Int)*fejerSum ts <
      ((harmonics : Int)+1-d)*(harmonics+1)*thresholdScale*thresholdScale :=
    of_decide_eq_true pass
  have rr : (d : ℝ)*fejerSum ts <
      ((harmonics : ℝ)+1-d)*(harmonics+1)*thresholdScale*thresholdScale := by exact_mod_cast u
  have weighted : (∑ k : Fin harmonics,
      fejerWeight harmonics k * (((ts[k.val]?.getD 0 : Int) : ℝ)/thresholdScale)^2) =
      (fejerSum ts : ℝ)/(((harmonics : ℝ)+1)*thresholdScale^2) := by
    rw [fejerSum_eq,Int.cast_sum,div_eq_mul_inv,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    unfold fejerWeight harmonics thresholdScale
    norm_num
    ring
  rw [weighted]
  norm_num [harmonics,thresholdScale] at rr ⊢
  apply (lt_sub_iff_add_lt).2
  apply (lt_div_iff₀ pos).2
  linarith

noncomputable def areaWeight (d : Nat) (r : Row) : ℝ :=
  if d == 23 || r.separate then 2*(r.area : ℝ)/CompleteWave.xInt else 0

noncomputable def meanValue (r : Row) : ℝ := (r.mean : ℝ) / quant

noncomputable def magnitudeValue (k : Nat) (r : Row) : ℝ :=
  ((r.magnitude[k]?.getD 0 : Int) : ℝ)/quant

noncomputable def thresholdValue (t : Int) : ℝ := (t : ℝ)/thresholdScale

noncomputable def nativeValue (d : Nat) (high : Int) : ℝ :=
  (high : ℝ)/((CompleteWave.xInt : ℝ)*quant*d)

private theorem rowCredit_real (r : Row) (d k : Nat) (t : Int) :
    areaWeight d r * max 0 (meanValue r + magnitudeValue k r * thresholdValue t) =
    (2/((CompleteWave.xInt : ℝ)*quant*thresholdScale)) *
      ((if d == 23 || r.separate then rowCredit r k t else 0 : Int) : ℝ) := by
  by_cases inc : (d == 23 || r.separate) = true
  · simp only [areaWeight, inc, if_true, rowCredit, Int.cast_mul, Int.cast_max, Int.cast_zero,
      Int.cast_add, meanValue,magnitudeValue,thresholdValue]
    set m : ℝ := (r.mean : ℝ)
    set a : ℝ := ((r.magnitude[k]?.getD 0 : Int) : ℝ)
    set w : ℝ := (t : ℝ)
    norm_num [CompleteWave.xInt,quant,thresholdScale]
    by_cases nonneg : 0 ≤ m * 100000 + w*a
    · rw [max_eq_right nonneg]
      rw [max_eq_right (by linarith : 0 ≤ m/10000000000+a/10000000000*(w/100000))]
      ring
    · rw [max_eq_left (le_of_not_ge nonneg)]
      rw [max_eq_left (by linarith : m/10000000000+a/10000000000*(w/100000) ≤ 0)]
      ring
  · simp [areaWeight,inc]

theorem harmonicScore_real (rows : Array Row) (d k : Nat) (high t : Int) :
    boxCredit Finset.univ (fun i : Fin rows.size => areaWeight d rows[i.val])
      (fun i => meanValue rows[i.val]) (fun i => magnitudeValue k rows[i.val])
      (nativeValue d high) (thresholdValue t) =
    nativeValue d high+2*harmonicScore rows d k t/((CompleteWave.xInt : ℝ)*quant*thresholdScale) := by
  unfold boxCredit harmonicScore
  rw [array_sum_by,Int.cast_sum]
  simp_rw [rowCredit_real]
  rw [← Finset.mul_sum]
  ring

/-- Each true degree Boolean implies the star estimate, once the exact
physical boxes give their Lemma 23 lower bounds and the phases satisfy Fejér. -/
theorem checkDegree_sound (rows : Array Row) (sat : Array (Int × Int)) (d : Nat) (hd : 0 < d)
    (s : Fin harmonics → ℝ) (score : ℝ)
    (ha : ∀ i : Fin rows.size, 0 ≤ areaWeight d rows[i.val])
    (hm : ∀ k : Fin harmonics, ∀ i : Fin rows.size, 0 ≤ magnitudeValue k.val rows[i.val])
    (hs : ∀ k, 0 ≤ s k ∧ s k ≤ 1)
    (box : ∀ k : Fin harmonics, boxCredit Finset.univ
      (fun i : Fin rows.size => areaWeight d rows[i.val]) (fun i => meanValue rows[i.val])
      (fun i => magnitudeValue k.val rows[i.val]) (nativeValue d (if d == 23 then 0 else nativeNumerator sat d))
      (s k) ≤ score)
    (fejer : (harmonics+1 : ℝ)/d-1 ≤ ∑ k, fejerWeight harmonics k*(s k)^2)
    (pass : checkDegree rows sat d = true) : (8 : ℝ)/10^9 ≤ score := by
  let hi := if d == 23 then 0 else nativeNumerator sat d
  let ts := thresholds d
  let t (k : Fin harmonics) := thresholdValue (ts[k.val]?.getD 0)
  refine threshold_test (d := d) (by decide : 0 < harmonics) Finset.univ
    (fun i : Fin rows.size => areaWeight d rows[i.val]) (fun i => meanValue rows[i.val])
    (fun k i => magnitudeValue k.val rows[i.val]) t s (nativeValue d hi) _ score
    (fun i _ => ha i) (fun k i _ => hm k i) hs box ?_ fejer ?_
  · intro k
    by_cases n : targetPass d hi 0 = true
    · apply Or.inr
      have small : (8 : ℝ)/10^9 ≤ nativeValue d hi := by
        simpa [nativeValue] using targetPass_sound d hd hi 0 n
      exact small.trans (le_add_of_nonneg_right (Finset.sum_nonneg
        fun i _ => mul_nonneg (ha i) (le_max_left ..)))
    · unfold checkDegree at pass
      change (targetPass d hi 0 || (fejerPass d ts && _) : Bool) = true at pass
      simp only [Bool.or_eq_true,Bool.and_eq_true,n,Bool.false_eq_true,false_or] at pass
      have h := (array_all_ofFn _).1 pass.2 k
      change harmonicPass rows d k.val hi (ts[k.val]?.getD 0) = true at h
      simp only [harmonicPass,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at h
      rcases h.2 with atOne | enough
      · left
        simp [t,thresholdValue,atOne,thresholdScale]
      · right
        rw [show t k = thresholdValue (ts[k.val]?.getD 0) from rfl,harmonicScore_real]
        exact targetPass_sound d hd hi _ enough
  · unfold checkDegree at pass
    change (targetPass d hi 0 || (fejerPass d ts && _) : Bool) = true at pass
    rw [Bool.or_eq_true,Bool.and_eq_true] at pass
    rcases pass with n|⟨fp,_⟩
    · left
      simpa [nativeValue] using targetPass_sound d hd hi 0 n
    · right
      exact fejerPass_sound d hd ts fp

end HadwigerNelson.Stars.BoxCheck

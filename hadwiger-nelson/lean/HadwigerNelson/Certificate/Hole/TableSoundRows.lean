import HadwigerNelson.Certificate.Hole.Tables
import HadwigerNelson.Blueprint.Point.ForestDefs
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

namespace HadwigerNelson.Certificate.Hole
open Forest Set
noncomputable section

def agrees (Ω : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y : ℚ, Ω (x:ℝ) y = (tickArea x y:ℝ)/(denom:ℝ)

theorem denom_pos : 0 < denom := by decide

theorem denom_pos_real : 0 < (denom:ℝ) := by exact_mod_cast denom_pos

theorem unitT_cast (i : ℕ) : (unitT i:ℝ) = unitBin i := by
  unfold unitT unitWidth unitBin Centres.w
  push_cast
  ring

theorem shortAt_value {Ω : ℝ → ℝ → ℝ} (val : agrees Ω) (r : ℚ) (i : ℕ) :
    ((shortAt r i:ℤ):ℝ)/(denom:ℝ) = lowerShort Ω r i := by
  unfold shortAt lowerShort
  rw [←val]
  unfold shortBin
  push_cast
  congr 1 <;> ring

private theorem rows_size (n : ℕ) : (unitRows n).size = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [unitRows_succ,Array.size_push,ih]

theorem unitRow_value {Ω : ℝ → ℝ → ℝ} (val : agrees Ω) (n j : ℕ) (hj : j ≤ n) :
    ((unitRows n)[j]?.getD 0:ℝ)/(denom:ℝ) = unitStep Ω j := by
  induction n generalizing j with
  | zero =>
    obtain rfl : j=0 := by omega
    simp [unitRows_zero,unitStep,denom_pos_real.ne']
  | succ n ih =>
    rw [unitRows_succ,Array.getElem?_push,rows_size]
    by_cases endpt : j=n+1
    · subst j
      simp only [if_true,Option.getD_some,Int.cast_min,unitStep]
      rw [← min_div_div_right denom_pos_real.le,ih n le_rfl]
      congr 1
      unfold unitAt
      rw [← val]
      simp only [Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,unitT_cast]
    · simp only [if_neg endpt]
      exact ih j (by omega)

theorem unitSum_value {Ω : ℝ → ℝ → ℝ} (val : agrees Ω) :
    ((unitSum (unitRows 16384):ℤ):ℝ)/(denom:ℝ) = ∑ i : Fin 16384, unitStep Ω (i.val+1) := by
  rw [unitSum,←Array.sum_toList,Array.toList_ofFn,List.sum_ofFn,Int.cast_sum,Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => unitRow_value val _ _ (by omega)

theorem retainedSum_value {Ω : ℝ → ℝ → ℝ} (val : agrees Ω) (M : ℚ) :
    (retainedSum (unitRows 16384) M : ℝ) = ∑ i : Fin 16384, max (unitStep Ω (i.val+1)-(M:ℝ)) 0 := by
  rw [retainedSum,←Array.sum_toList,Array.toList_ofFn,List.sum_ofFn,Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  rw [unitRow_value val _ _ (by omega)]

theorem shortRows_get (r : ℚ) (i : Fin 8192) :
    (shortRows r)[i.val]?.getD 0 = shortAt r i.val := by simp [shortRows,i.isLt]

private theorem shortMax_le (A : Array ℤ) (b : ℤ) :
    shortMax A ≤ b ↔ 0≤b ∧ ∀ x∈A, x≤b := by
  rw [shortMax,← Array.foldl_toList]
  simp only [← Array.mem_toList_iff]
  generalize A.toList = L
  generalize (0:ℤ) = z
  induction L generalizing z with
  | nil => simp
  | cons a L ih => simp [List.foldl_cons,ih,and_assoc]

private theorem row_max (r : ℚ) (h : 0≤shortAt r 0) :
    ∃ j : Fin 8192, shortMax (shortRows r)=shortAt r j.val ∧
      ∀ i : Fin 8192, shortAt r i.val ≤ shortAt r j.val := by
  obtain ⟨j,_,top⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 8192)) (fun i => shortAt r i.val) Finset.univ_nonempty
  have upper (i : Fin 8192) := top i (Finset.mem_univ i)
  have mem (i : Fin 8192) : shortAt r i.val ∈ shortRows r := Array.mem_ofFn.mpr ⟨i,rfl⟩
  refine ⟨j,le_antisymm ?_ ?_,upper⟩
  · apply (shortMax_le ..).mpr
    refine ⟨h.trans (upper 0),?_⟩
    intro x hx
    obtain ⟨i,e⟩ := Array.mem_ofFn.mp hx
    exact e ▸ upper i
  · exact ((shortMax_le ..).mp (le_rfl : shortMax (shortRows r) ≤ _)).2 _ (mem j)

theorem shortCap_value {Ω : ℝ → ℝ → ℝ} (val : agrees Ω) (r f : ℚ) (h : 0≤shortAt r 0)
    (fac : (f:ℝ) = if (r:ℝ) = a then 3/4 else 3/10) :
    (shortCap (shortRows r) f:ℝ) = cap Ω r := by
  obtain ⟨j,eq,top⟩ := row_max r h
  have peak : sSup (Set.range fun i : Fin 8192 => lowerShort Ω r i.val) = lowerShort Ω r j.val := by
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro u ⟨i,rfl⟩
      change lowerShort Ω r i.val ≤ lowerShort Ω r j.val
      rw [←shortAt_value val,←shortAt_value val]
      exact div_le_div_of_nonneg_right (by exact_mod_cast top i) denom_pos_real.le
    · exact le_csSup (Finite.bddAbove_range _) ⟨j,rfl⟩
  simp only [shortCap,cap,Rat.cast_div,Rat.cast_mul,Rat.cast_intCast,fac,peak,eq]
  rw [mul_div_assoc,shortAt_value val]

end
end HadwigerNelson.Certificate.Hole

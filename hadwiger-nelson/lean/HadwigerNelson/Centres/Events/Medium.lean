import HadwigerNelson.Centres.Events.Runtime
import HadwigerNelson.Certificate.Hole.Physical
import Mathlib.Analysis.Real.Pi.Bounds

namespace HadwigerNelson.Centres.Quadrature
open Wave

theorem rootGuard_sound {q : ℚ} (ok : rootGuard q = true) :
    0≤(q:ℝ) ∧ (q:ℝ)≤2 ∧ 0≤(deficit q:ℝ) ∧
    (2-(deficit q:ℝ))^2 ≤ 4-(q:ℝ)^2 := by
  simp only [rootGuard,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨a,b⟩,c⟩,_⟩,e⟩ := ok
  exact ⟨by exact_mod_cast a,by exact_mod_cast b,by exact_mod_cast c,by exact_mod_cast e⟩

theorem deficit_upper {q : ℚ} (ok : rootGuard q = true) :
    2-Real.sqrt (4-(q:ℝ)^2) ≤ (deficit q:ℝ) := by
  linarith [Real.le_sqrt_of_sq_le (rootGuard_sound ok).2.2.2]

theorem sag_upper {q : ℚ} (ok : rootGuard q = true) :
    1-Real.sqrt (1-(q:ℝ)^2/4) ≤ (deficit q:ℝ)/2 := by
  have h : (1-(deficit q:ℝ)/2)^2 ≤ 1-(q:ℝ)^2/4 := by nlinarith [(rootGuard_sound ok).2.2.2]
  linarith [Real.le_sqrt_of_sq_le h]

theorem angle_upper : Real.pi ≤ (piHi:ℝ) := by
  norm_num [piHi]
  linarith [Real.pi_lt_d20]

theorem cast_array_sum {n : Nat} (f : Fin n → ℚ) :
    (((Array.ofFn f).sum : ℚ) : ℝ) = ∑ i, (f i : ℝ) := by
  rw [←Array.sum_toList,Array.toList_ofFn,List.sum_ofFn,Rat.cast_sum]

/-- A lower bound on the sum of true conditional overlaps for any choice of
one displacement in each of the angular bins of a medium chord interval. -/
theorem mediumPass_real (W : Datum) (hW : partialProfile W) (fine : Bool) (i : Nat)
    (ok : mediumPass fine i = true) (v : Fin (mAngles fine) → Plane)
    (hx : ∀ j, |v j 0| ≤ ((2*((j.val+1 : Nat)*(mEnd (breakpoint i)/mAngles fine)):ℚ):ℝ))
    (hy : ∀ j, |v j 1| ≤ ((deficit (breakpoint (i+1))+((j.val+1 : Nat)*(mEnd (breakpoint i)/mAngles fine))^2:ℚ):ℝ)) :
    (mTarget fine (breakpoint i):ℝ) ≤
      2*((mEnd (breakpoint i)/mAngles fine:ℚ):ℝ)/Real.pi*
        ∑ j, holeCovariogram W (v j)/(2*W.x*H) := by
  simp only [mediumPass,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨_,ang⟩,lower⟩ := ok
  let dt : ℚ := mEnd (breakpoint i)/mAngles fine
  have nd : 0 < mAngles fine := by cases fine <;> decide
  have hd : 0 ≤ (dt:ℝ) := by exact_mod_cast (show (0:ℚ)≤dt from div_nonneg ang.le (by positivity))
  have q := Rat.cast_le (K:=ℝ) |>.mpr lower
  rw [mediumTotal,Rat.cast_mul,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,cast_array_sum] at q
  have term (j : Fin (mAngles fine)) : 0 ≤ (mediumTerm fine i j.val : ℝ) ∧
      (mediumTerm fine i j.val:ℝ) ≤ holeCovariogram W (v j)/(2*W.x*H) := by
    have s := Certificate.Hole.physical_sound W hW _ _ (v j) (hx j) (hy j)
    rw [Certificate.Hole.physical_rat] at s
    exact s
  have ps : 0 ≤ ∑ j : Fin (mAngles fine), (mediumTerm fine i j.val:ℝ) :=
    Finset.sum_nonneg fun j _ => (term j).1
  refine q.trans (mul_le_mul ?_ (Finset.sum_le_sum (fun j _ => (term j).2)) ps (by positivity))
  exact div_le_div_of_nonneg_left (by positivity) Real.pi_pos angle_upper

def mediumCheck (fine : Bool) : Bool := (Array.range 61).all (mediumPass fine)

theorem mediumCheck_each {fine : Bool} (ok : mediumCheck fine = true) (i : Fin 61) :
    mediumPass fine i.val = true := by
  have h := Array.all_eq_true.mp ok i.val (by simp)
  simpa using h

end HadwigerNelson.Centres.Quadrature

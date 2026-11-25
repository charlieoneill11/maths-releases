import HadwigerNelson.Certificate.Hole.TableSoundRows
import HadwigerNelson.Certificate.Hole.Physical
import Mathlib.Analysis.Real.Pi.Bounds

namespace HadwigerNelson.Certificate.Hole
open Forest Set
noncomputable section

theorem physical_agrees : agrees physical := by
  intro x y
  rw [physical_rat]
  unfold overlap tickArea denom
  push_cast
  rfl

private theorem weighted_floor (h : ℚ) (i : ℕ) :
    (weightedTicks h i:ℝ)/(weightScale:ℝ) ≤ (h:ℝ)*(shortWeight i:ℝ) := by
  have sc : (0:ℝ)<(weightScale:ℝ) := by norm_num [weightScale]
  apply (div_le_iff₀ sc).mpr
  have f := Int.floor_le (h*shortWeight i*weightScale)
  exact_mod_cast f

private theorem shortWeight_cast (i : ℕ) : (shortWeight i:ℝ) =
    2*(shortBin (i+1)-shortBin i)/(1+shortBin (i+1)^2) := by
  unfold shortWeight shortBin
  push_cast
  ring

private theorem clippedMean_le {Ω : ℝ → ℝ → ℝ} (val : agrees Ω) (r M : ℚ) (eq : (M:ℝ)=cap Ω r) :
    (clippedMean (shortRows r) M:ℝ) ≤ lowerShortMean Ω r := by
  unfold clippedMean lowerShortMean
  push_cast
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [shortSum,←Array.sum_toList,Array.toList_ofFn,List.sum_ofFn,Int.cast_sum,Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  apply (weighted_floor _ _).trans_eq
  rw [shortRows_get,shortWeight_cast]
  simp only [Rat.cast_min,Rat.cast_div,Rat.cast_intCast,eq,shortAt_value val,cappedShort]

private theorem firstRow_nonneg (r : ℚ) (hr : 0≤r) : 0 ≤ shortAt r 0 := by
  have s := physical_sound PartialWave.datum
    ⟨PartialWave.datum_x,PartialWave.datum_y0,PartialWave.datum_left_segment⟩
  have pos (x y : ℝ) (hx : 0≤x) (hy : 0≤y) : 0≤physical x y :=
    (s x y 0 (by simpa using hx) (by simpa using hy)).1
  have hr' : 0≤(r:ℝ) := by exact_mod_cast hr
  have h : 0≤lowerShort physical r 0 := by
    unfold lowerShort shortBin
    apply pos <;> norm_num <;> positivity
  rw [←shortAt_value physical_agrees] at h
  have hh := (le_div_iff₀ denom_pos_real).mp h
  rw [zero_mul] at hh
  exact_mod_cast hh

private theorem radiusR_cast : (radiusR:ℝ)=a := by norm_num [radiusR,a,Centres.δR]
private theorem radiusD_cast : (radiusD:ℝ)=d := by norm_num [radiusD,d,Centres.δ]
private theorem unitWidth_cast : (unitWidth:ℝ)=unitBin 1 := by norm_num [unitWidth,unitBin,Centres.w]

/-- The unit and short edge averages and the two retained fractions all
refer to the same physical overlap function and its exact finite caps. -/
theorem checkMeans_sound (ok : checkMeans = true) :
    112668096940/(10:ℝ)^18 ≤ unitMean physical ∧
    16034576942481/(10:ℝ)^18 ≤ lowerShortMean physical a ∧
    3057937052494/(10:ℝ)^18 ≤ lowerShortMean physical d ∧
    344/1000 ≤ retention physical (cap physical a) ∧
    761/1000 ≤ retention physical (cap physical d) := by
  let ur := unitRows 16384
  let total : ℚ := (unitSum ur:ℚ)/denom
  let rc := shortCap (shortRows radiusR) (3/4)
  let dc := shortCap (shortRows radiusD) (3/10)
  have checked : (112668096940/10^18 : ℚ) ≤ 2*unitWidth/(355/113)*total ∧
      (16034576942481/10^18 : ℚ) ≤ clippedMean (shortRows radiusR) rc ∧
      (3057937052494/10^18 : ℚ) ≤ clippedMean (shortRows radiusD) dc ∧
      0 < total ∧ 344/1000*total ≤ retainedSum ur rc ∧ 761/1000*total ≤ retainedSum ur dc :=
    of_decide_eq_true ok
  obtain ⟨u,b,c,positive,retR,retD⟩ := checked
  have rEq : (rc:ℝ)=cap physical radiusR := shortCap_value physical_agrees _ _ (firstRow_nonneg _ (by norm_num [radiusR]))
    (by rw [radiusR_cast,if_pos rfl]; norm_num)
  have dEq : (dc:ℝ)=cap physical radiusD := shortCap_value physical_agrees _ _ (firstRow_nonneg _ (by norm_num [radiusD]))
    (by rw [radiusD_cast,if_neg (by norm_num [d,a,Centres.δR,Centres.δ])]; norm_num)
  have totalEq : (total:ℝ) = ∑ i : Fin 16384, unitStep physical (i.val+1) := by
    dsimp only [total,ur]; push_cast; exact unitSum_value physical_agrees
  have pos : 0 < (total:ℝ) := by exact_mod_cast positive
  have rb : (16034576942481/(10:ℝ)^18) ≤ (clippedMean (shortRows radiusR) rc:ℝ) := by
      simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).2 b
  have db : (3057937052494/(10:ℝ)^18) ≤ (clippedMean (shortRows radiusD) dc:ℝ) := by
      simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).2 c
  refine ⟨?_,radiusR_cast ▸ rb.trans (clippedMean_le physical_agrees _ _ rEq),
    radiusD_cast ▸ db.trans (clippedMean_le physical_agrees _ _ dEq),?_,?_⟩
  · have a : (112668096940/(10:ℝ)^18) ≤ 2*(unitWidth:ℝ)/(355/113)*(total:ℝ) := by
      simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).2 u
    rw [unitWidth_cast] at a
    rw [unitMean,←totalEq]
    apply a.trans (mul_le_mul_of_nonneg_right _ pos.le)
    exact div_le_div_of_nonneg_left (by norm_num [unitBin,Centres.w]) Real.pi_pos
      (by linarith [Real.pi_lt_d20])
  · have h : (344/1000:ℝ)*(total:ℝ) ≤ (retainedSum ur rc:ℝ) := by
      simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).2 retR
    rw [retention,←totalEq,le_div_iff₀ pos]
    rw [retainedSum_value physical_agrees,rEq,radiusR_cast] at h
    exact h
  · have h : (761/1000:ℝ)*(total:ℝ) ≤ (retainedSum ur dc:ℝ) := by
      simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).2 retD
    rw [retention,←totalEq,le_div_iff₀ pos]
    rw [retainedSum_value physical_agrees,dEq,radiusD_cast] at h
    exact h

end
end HadwigerNelson.Certificate.Hole

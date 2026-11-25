import HadwigerNelson.Forest.Rotations
import HadwigerNelson.Blueprint.Point.ForestDefs
import HadwigerNelson.Arithmetic.Rays

/-! The folded half-angle and vertical angular bins of Lemma 34, with the
signed coordinate bounds used by the hole covariogram. -/

namespace HadwigerNelson.Forest
open Arithmetic Centres Wave
noncomputable section

private theorem folded_ray {A B R : ℝ} (ha : 0 ≤ A) (hb : 0 ≤ B) (hr : 0<R)
    (unit : A^2+B^2=R^2) :
    let t := B/(R+A)
    t∈Set.Icc 0 1 ∧ R*rayX t=A ∧ R*rayY t=B := by
  intro t
  have hp : 0 < R+A := by linarith
  have bR : B ≤ R := by nlinarith [sq_nonneg A,sq_nonneg (R-B)]
  have den : 1+t^2 = 2*R/(R+A) := by
    dsimp [t]
    field_simp
    linarith only [unit]
  refine ⟨⟨div_nonneg hb hp.le,(div_le_one hp).mpr (by linarith)⟩,?_,?_⟩
  · have reform : rayX t = 2/(1+t^2)-1 := by unfold rayX; field_simp; ring
    rw [reform,den]
    field_simp
    ring
  · rw [rayY,den]
    dsimp [t]
    field_simp

private theorem bin_loc (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    let i := min 8191 ⌊8192*t⌋₊
    shortBin i ≤ t ∧ t ≤ shortBin (i+1) ∧ shortBin (i+1) ≤ 1 := by
  intro i
  have hlow := Nat.floor_le (show 0 ≤ 8192*t by linarith [ht.1])
  have hupp := Nat.lt_floor_add_one (8192*t)
  have ib : i ≤ 8191 := min_le_left ..
  have ff : i ≤ ⌊8192*t⌋₊ := min_le_right ..
  have ff' : (i:ℝ) ≤ (⌊8192*t⌋₊:ℝ) := by exact_mod_cast ff
  have cut : (i:ℝ)≤8191 := by exact_mod_cast ib
  simp only [shortBin,Nat.cast_add,Nat.cast_one]
  refine ⟨by linarith,?_,by linarith⟩
  by_cases h : 8191 ≤ ⌊8192*t⌋₊
  · have eq : i=8191 := min_eq_left h
    rw [eq]
    norm_num
    exact ht.2
  · have eq : i=⌊8192*t⌋₊ := min_eq_right (le_of_not_ge h)
    rw [eq]; linarith

theorem short_box {ρ : ℝ} {v : Plane} (hv : 0<‖v‖) (hr : ‖v‖≤2*ρ) :
    let i := shortIndex v
    let lo := shortBin i
    let hi := shortBin (i+1)
    |v 0| ≤ 2*ρ*(1-lo^2)/(1+lo^2) ∧ |v 1| ≤ 2*ρ*2*hi/(1+hi^2) := by
  let t := |v 1|/(‖v‖+|v 0|)
  have unit : |v 0|^2+|v 1|^2=‖v‖^2 := by
    simpa [sq_abs] using (Placement.coord_dist_sq v 0).symm
  obtain ⟨ht,ray0,ray1⟩ := folded_ray (abs_nonneg _) (abs_nonneg _) hv unit
  let i := shortIndex v
  have index : i = min 8191 ⌊8192*t⌋₊ := by simp only [i,shortIndex,t,mul_div_assoc]
  have bounds := bin_loc t ht
  rw [← index] at bounds
  have lo : 0≤shortBin i := by unfold shortBin; positivity
  have lo1 : shortBin i ≤ 1 := bounds.1.trans ht.2
  have posX : 0 ≤ rayX (shortBin i) := by
    apply div_nonneg _ (by positivity)
    nlinarith [mul_nonneg lo (sub_nonneg.mpr lo1),mul_nonneg (sub_nonneg.mpr lo1) (by linarith : 0≤1+shortBin i)]
  have posY : 0 ≤ rayY (shortBin (i+1)) := by
    unfold rayY shortBin; positivity
  change _ ≤ _ ∧ _ ≤ _
  have x := mul_le_mul hr (rayX_antitone lo bounds.1) (by
    have le1 := ht.2; have le0 := ht.1
    change 0 ≤ (1-(_)^2)/(1+(_)^2)
    apply div_nonneg _ (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr le1) (add_nonneg zero_le_one le0)]) (by linarith)
  have y := mul_le_mul hr (rayY_monotone ht.1 bounds.2.1 bounds.2.2) (by
    apply div_nonneg (mul_nonneg (by norm_num) ht.1) (by positivity)) (by linarith)
  rw [ray0] at x
  rw [ray1] at y
  constructor
  · simpa only [rayX,mul_div_assoc,i] using x
  · simpa only [rayY,mul_div_assoc,mul_assoc,i] using y

theorem unit_bin_upper {t : ℝ} (ht : |t| ≤ w) :
    let k := min 16384 (max 1 ⌈|t|/unitBin 1⌉₊)
    1 ≤ k ∧ |t| ≤ unitBin k := by
  intro k
  have hb : 0 < unitBin 1 := by norm_num [unitBin,w]
  have cap : ⌈|t|/unitBin 1⌉₊ ≤ 16384 := Nat.ceil_le.mpr (by
    apply (div_le_iff₀ hb).mpr; convert ht using 1; norm_num [unitBin,w])
  have eq : k=max 1 ⌈|t|/unitBin 1⌉₊ := min_eq_right (max_le (by decide) cap)
  have ub := Nat.le_ceil (|t|/unitBin 1)
  have raw : ⌈|t|/unitBin 1⌉₊ ≤ k := eq ▸ le_max_right ..
  have raw' : (⌈|t|/unitBin 1⌉₊:ℝ) ≤ k := by exact_mod_cast raw
  have fin := (div_le_iff₀ hb).mp (ub.trans raw')
  refine ⟨eq ▸ le_max_left ..,?_⟩
  convert fin using 1
  simp [unitBin,mul_div_assoc]

theorem blank_credits_from_holes (W : Datum) (Ω : ℝ → ℝ → ℝ) (sound : holeEnclosure W Ω)
    (holes : ∀ v : Plane, max (holeCovariogram W v) (holeCovariogram W (v-point 0 1)) /
      (2*W.x*H) ≤ bothBlank W v) :
    (∀ (ρ : ℝ) (v : Plane), 0<‖v‖ → ‖v‖≤2*ρ →
      lowerShort Ω ρ (shortIndex v) ≤ bothBlank W v) ∧
    (∀ t : ℝ, |t|≤w → unitCredit Ω t ≤ bothBlank W (point (Real.sin t) (Real.cos t))) := by
  have positive : 0 ≤ 2*W.x*H := by nlinarith [W.x_bounds.1,H_pos,mul_pos (by linarith [W.x_bounds.1] : 0<2*W.x) H_pos]
  constructor
  · intro ρ v hv hr
    obtain ⟨hx,hy⟩ := short_box hv hr
    exact (sound _ _ v hx hy).2.trans ((div_le_div_of_nonneg_right (le_max_left ..) positive).trans (holes v))
  · intro t ht
    let k := min 16384 (max 1 ⌈|t|/unitBin 1⌉₊)
    obtain ⟨hk,hu⟩ := unit_bin_upper ht
    let z := point (Real.sin t) (Real.cos t)
    have hx : |(z-point 0 1) 0| ≤ unitBin k := by simpa [z] using Real.abs_sin_le_abs.trans hu
    have hy : |(z-point 0 1) 1| ≤ (unitBin k)^2/2 := by
      change |Real.cos t-1| ≤ _
      rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one _))]
      have q := (sq_abs t).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) hu 2)
      linarith [Real.one_sub_sq_div_two_le_cos (x:=t)]
    have le := (sound _ _ (z-point 0 1) hx hy).2
    have low : unitStep Ω k ≤ Ω (unitBin k) ((unitBin k)^2/2) := by
      change 1 ≤ k at hk
      obtain ⟨k',eq⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
      rw [eq]; exact min_le_right ..
    exact low.trans (le.trans ((div_le_div_of_nonneg_right (le_max_right ..) positive).trans (holes z)))

end
end HadwigerNelson.Forest

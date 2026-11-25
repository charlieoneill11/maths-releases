import HadwigerNelson.Blueprint.Point.ForestDefs
import HadwigerNelson.Forest.Rotations
import HadwigerNelson.Placement.BlankHoles
import HadwigerNelson.Wave.Geometry.PartialProfile

/-! The two unit tails of Lemma 36 must occupy one narrow column when both are blank. -/

namespace HadwigerNelson.Forest
open Centres Placement MeasureTheory Set
noncomputable section

private theorem zero_width (W : Wave.Datum) (hW : partialProfile W) :
    W.left 0 = 3673765364/10^12 := by
  have hp := hW.2.2 (0 : Fin 17) 0 ⟨le_rfl,zero_le_one⟩
  have first : (PartialWave.leftKnot 0).2 = 3673765364 := by decide +kernel
  norm_num at hp
  norm_num [first] at hp ⊢
  exact hp

private theorem column {W : Wave.Datum} {z : Plane} (hz : z ∈ Wave.holeCopies W) :
    ∃ i : ℤ, |z 0-2*W.x*i| ≤ W.left 0 := by
  obtain ⟨i,j,hm⟩ := hz
  let y := (z-Wave.holeLatticePoint W i j) 1
  have hy : |y| ≤ W.y0 := hm.1
  have ha : W.left |y| = W.left y := by
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h,W.left_even]
  have hle : W.left |y| ≤ W.left 0 := W.left_antitone ⟨le_rfl,by norm_num [Wave.H]⟩
    ⟨abs_nonneg _,by linarith [W.y0_bounds.2,Wave.H_pos]⟩ (abs_nonneg _)
  exact ⟨i,hm.2.trans (ha ▸ hle)⟩

private theorem same_column (W : Wave.Datum) (hW : partialProfile W) (z z' : Plane)
    (hz : z ∈ Wave.holeCopies W) (hz' : z' ∈ Wave.holeCopies W)
    (near : |z 0-z' 0| ≤ 2*w) : |z 0-z' 0| ≤ 2*W.left 0 := by
  obtain ⟨i,hi⟩ := column hz
  obtain ⟨j,hj⟩ := column hz'
  obtain ⟨hil,hir⟩ := abs_le.mp hi
  obtain ⟨hjl,hjr⟩ := abs_le.mp hj
  obtain ⟨hnl,hnr⟩ := abs_le.mp near
  have width := zero_width W hW
  have step : 0 < 2*W.x := by linarith [W.x_bounds.1]
  have eq : i=j := by
    rcases lt_trichotomy i j with lt | eq | gt
    · have gap : (i:ℝ)+1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
      have s := mul_le_mul_of_nonneg_left gap step.le
      norm_num [w] at *
      linarith [W.x_bounds.1]
    · exact eq
    · have gap : (j:ℝ)+1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
      have s := mul_le_mul_of_nonneg_left gap step.le
      norm_num [w] at *
      linarith [W.x_bounds.1]
  subst j
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private theorem cos_band {t : ℝ} (ht : |t| ≤ w) :
    1-w^2/2 ≤ Real.cos t ∧ Real.cos t ≤ 1 := by
  have sq := (sq_abs t).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) ht 2)
  exact ⟨(sub_le_sub_left (div_le_div_of_nonneg_right sq (by norm_num : (0:ℝ)≤2)) 1).trans Real.one_sub_sq_div_two_le_cos,Real.cos_le_one _⟩

theorem two_inner_tails (W : Wave.Datum) (hW : partialProfile W) (D : Finset Plane)
    (sep : Packing.separated D δ) (x x' y : Plane) (hx : x ∈ D) (hx' : x' ∈ D)
    (ne : x≠x') (θ : ℝ) (h₁ : unitCandidate θ x y) (h₂ : unitCandidate θ x' y) :
    ∀ᵐ τ ∂translationLaw W, ¬(colour W (θ,τ) x = none ∧ colour W (θ,τ) x' = none) := by
  obtain ⟨t,ht,ut⟩ := h₁
  obtain ⟨s,hs,us⟩ := h₂
  rw [rotate_sub] at ut us
  have diff (i : Fin 2) := congrArg (fun v : Plane => v i) ut
  have diff' (i : Fin 2) := congrArg (fun v : Plane => v i) us
  have ht0 := diff 0
  have hs0 := diff' 0
  have ht1 := diff 1
  have hs1 := diff' 1
  simp only [PiLp.sub_apply,Wave.point_fst,Wave.point_snd] at ht0 hs0 ht1 hs1
  have sn := abs_le.mp (Real.abs_sin_le_abs.trans ht)
  have sn' := abs_le.mp (Real.abs_sin_le_abs.trans hs)
  have cs := cos_band ht
  have cs' := cos_band hs
  have dx : |rotate θ x 0-rotate θ x' 0| ≤ 2*w := abs_le.mpr ⟨by linarith,by linarith⟩
  have dy : |rotate θ x 1-rotate θ x' 1| ≤ w^2/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  filter_upwards [placed_blank_in_holes W θ x,placed_blank_in_holes W θ x'] with τ h h'
  rintro ⟨hb,hb'⟩
  have hsame := same_column W hW (place (θ,τ) x) (place (θ,τ) x') (h hb) (h' hb')
    (by simpa [place,add_sub_add_right_eq_sub] using dx)
  simp only [place,PiLp.add_apply,add_sub_add_right_eq_sub] at hsame
  have sx := pow_le_pow_left₀ (abs_nonneg _) hsame 2
  have sy := pow_le_pow_left₀ (abs_nonneg _) dy 2
  rw [sq_abs,zero_width W hW] at sx
  rw [sq_abs] at sy
  have sd := sep x hx x' hx' ne
  rw [← rotate_dist θ] at sd
  have far := pow_lt_pow_left₀ sd (show 0 ≤ δ by norm_num [δ]) (by decide : 2≠0)
  rw [coord_dist_sq] at far
  norm_num [δ,w] at far sx sy
  linarith

end
end HadwigerNelson.Forest

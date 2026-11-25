import HadwigerNelson.Wave.Holes.Monotone
import HadwigerNelson.Arithmetic.Positive

namespace HadwigerNelson.Wave
open MeasureTheory Set Arithmetic
noncomputable section

theorem tickDown_le (v : ℝ) : tickDown v ≤ v := by
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<10^12)).mpr
  exact Int.floor_le _

theorem le_tickUp (v : ℝ) : v ≤ tickUp v := by
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<10^12)).mpr
  exact Int.le_ceil _

private theorem areaDown_le (v : ℝ) : areaDown v ≤ v := by
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2*10^24)).mpr
  convert Int.floor_le (2*v*10^24) using 1 <;> ring

private theorem areaDown_nonneg {v : ℝ} (hv : 0≤v) : 0≤areaDown v := by
  apply div_nonneg _ (by norm_num)
  exact_mod_cast Int.floor_nonneg.mpr (by positivity : 0≤2*v*10^24)

private theorem positiveChord_nonneg (u v : ℝ) : 0≤positiveChord u v := by
  unfold positiveChord
  split_ifs with a b b <;> first | positivity | exact div_nonneg (sq_nonneg _) (by linarith) | linarith

private theorem chord_eq_area (u v w : ℝ) : 2*(w*positiveChord u v) = positiveArea2 u v w := by
  rcases lt_trichotomy u 0 with hu | rfl | hu <;>
    rcases lt_trichotomy v 0 with hv | rfl | hv <;>
    simp only [positiveChord,positiveArea2,min_def,max_def] <;>
    split_ifs <;> first | (exfalso; linarith) | (simp [div_eq_mul_inv,mul_inv_rev] <;> ring)

private def vertex (W : Datum) (X Y t : ℝ) : ℝ :=
  let a := tickDown (W.left t)
  let b := tickDown (W.left (t-Y))
  min (2*a) (min (2*b) (a+b-X))

private theorem vertex_le (W : Datum) (X Y t : ℝ) :
    vertex W X Y t ≤ 2*W.left t ∧ vertex W X Y t ≤ 2*W.left (t-Y) ∧
      vertex W X Y t ≤ W.left t + W.left (t-Y) - X := by
  let a := tickDown (W.left t)
  let b := tickDown (W.left (t-Y))
  have h : vertex W X Y t ≤ 2*a ∧ vertex W X Y t ≤ 2*b ∧ vertex W X Y t ≤ a+b-X :=
    ⟨min_le_left ..,(min_le_right ..).trans (min_le_left ..),(min_le_right ..).trans (min_le_right ..)⟩
  have la : a≤W.left t := tickDown_le _
  have lb : b≤W.left (t-Y) := tickDown_le _
  exact ⟨by linarith [h.1],by linarith [h.2.1],by linarith [h.2.2]⟩

private theorem chord_below_affine {l r p q a b t : ℝ} (lt : l<r) (ht : t∈Icc l r)
    (hp : p≤a*l+b) (hq : q≤a*r+b) : linearAt l p r q t ≤ a*t+b := by
  apply (linearAt_mono lt ht.1 ht.2 hp hq).trans_eq
  unfold linearAt
  field_simp [(sub_pos.mpr lt).ne']; ring

private theorem segment_bound (W : Datum) (X Y l r : ℝ) (le : l≤r)
    (h₁ : ∃ a b : ℝ, ∀ t∈Icc l r, W.left t = a*t+b)
    (h₂ : ∃ a b : ℝ, ∀ t∈Icc l r, W.left (t-Y) = a*t+b) :
    areaDown ((r-l)*positiveChord (vertex W X Y l) (vertex W X Y r)) ≤
      ∫ t in l..r, holeSlice (W.left t) (W.left (t-Y)) X := by
  apply (areaDown_le _).trans
  rcases le.eq_or_lt with eq | lt
  · subst r; simp
  let p := vertex W X Y l
  let q := vertex W X Y r
  let f := fun t : ℝ => holeSlice (W.left t) (W.left (t-Y)) X
  have a := integral_positive_linearAt l r p q lt
  rw [←chord_eq_area] at a
  change (r-l)*positiveChord p q ≤ _
  rw [show (r-l)*positiveChord p q = ∫ t in l..r, max 0 (linearAt l p r q t) by linarith only [a]]
  apply intervalIntegral.integral_mono_on le
  · apply Continuous.intervalIntegrable
    unfold linearAt
    fun_prop
  · have hc := W.left_continuous
    apply Continuous.intervalIntegrable
    unfold holeSlice
    fun_prop (disch := assumption)
  intro t ht
  obtain ⟨a,b,h₁⟩ := h₁
  obtain ⟨c,d,h₂⟩ := h₂
  have hp := vertex_le W X Y l
  have hq := vertex_le W X Y r
  rw [h₁ l ⟨le_rfl,le⟩,h₂ l ⟨le_rfl,le⟩] at hp
  rw [h₁ r ⟨le,le_rfl⟩,h₂ r ⟨le,le_rfl⟩] at hq
  change max 0 (linearAt l p r q t) ≤ _
  apply max_le_max_left
  rw [h₁ t ht,h₂ t ht]
  apply le_min _ (le_min _ _)
  · have h := chord_below_affine (p:=p) (q:=q) (a:=2*a) (b:=2*b) lt ht
      (by dsimp [p]; linarith [hp.1]) (by dsimp [q]; linarith [hq.1])
    linarith
  · have h := chord_below_affine (p:=p) (q:=q) (a:=2*c) (b:=2*d) lt ht
      (by dsimp [p]; linarith [hp.2.1]) (by dsimp [q]; linarith [hq.2.1])
    linarith
  · have h := chord_below_affine (p:=p) (q:=q) (a:=a+c) (b:=b+d-X) lt ht
      (by dsimp [p]; linarith [hp.2.2]) (by dsimp [q]; linarith [hq.2.2])
    linarith

private theorem integrate_grid {k : ℕ} (grid : Fin (k+1) → ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    (∑ i : Fin k, ∫ t in grid i.castSucc..grid i.succ, f t) =
      ∫ t in grid 0..grid (Fin.last k), f t := by
  let a (n : ℕ) := grid ⟨min n k,by omega⟩
  have s := intervalIntegral.sum_integral_adjacent_intervals (μ:=volume) (n:=k) (a:=a)
    (fun i _ => hf.intervalIntegrable (a i) (a (i+1)))
  rw [←Fin.sum_univ_eq_sum_range] at s
  convert s using 1
  · apply Finset.sum_congr rfl
    intro i _
    have l : a i = grid i.castSucc := congrArg grid (Fin.ext (Nat.min_eq_left (by omega)))
    have r : a (i+1) = grid i.succ := congrArg grid (Fin.ext (Nat.min_eq_left (by omega)))
    rw [l,r]
  · simp [a,Fin.last]

/-- The clipped affine chords on the merged breakpoint list under-approximate
the area at the rounded displacement, and moving the two centres towards
each other can only enlarge the overlap. -/
theorem holeLower_bound {k : ℕ} (W : Datum) (x y : ℝ) (grid : Fin (k+1) → ℝ)
    (hg : tickUp y < 2*W.y0 → holePartition W (tickUp y) grid)
    (v : Plane) (hx : |v 0|≤x) (hy : |v 1|≤y) :
    0 ≤ holeLower W x y grid ∧ holeLower W x y grid ≤ holeCovariogram W v/(2*W.x*H) := by
  let X := tickUp x
  let Y := tickUp y
  have den : 0<2*W.x*H := by nlinarith [W.x_bounds.1,H_pos]
  have X0 : 0≤X := (abs_nonneg _).trans (hx.trans (le_tickUp x))
  have Y0 : 0≤Y := (abs_nonneg _).trans (hy.trans (le_tickUp y))
  by_cases zero : 2*W.y0 ≤ Y
  · rw [holeLower,if_pos zero]
    exact ⟨le_rfl,div_nonneg ENNReal.toReal_nonneg den.le⟩
  · obtain ⟨first,last,mono,aff⟩ := hg (lt_of_not_ge zero)
    let f := fun t : ℝ => holeSlice (W.left t) (W.left (t-Y)) X
    have hc := W.left_continuous
    have fc : Continuous f := by dsimp [f,holeSlice]; fun_prop (disch := assumption)
    have low := integrate_grid grid f fc
    rw [first,last] at low
    have cov := hole_horizontal_formula W X Y X0 Y0
    rw [←intervalIntegral.integral_of_le (show Y-W.y0≤W.y0 by linarith),←low] at cov
    have mv := holeCovariogram_antitone W v (point X Y)
      (by simpa only [point_fst,abs_of_nonneg X0] using hx.trans (le_tickUp x))
      (by simpa only [point_snd,abs_of_nonneg Y0] using hy.trans (le_tickUp y))
    rw [holeLower,if_neg zero]
    constructor
    · apply div_nonneg _ den.le
      apply Finset.sum_nonneg
      intro i _
      exact areaDown_nonneg (mul_nonneg (sub_nonneg.mpr (mono (Fin.castSucc_le_succ i))) (positiveChord_nonneg ..))
    · apply div_le_div_of_nonneg_right _ den.le
      apply le_trans _ mv
      rw [cov]
      apply Finset.sum_le_sum
      intro i _
      exact segment_bound W X Y _ _ (mono (Fin.castSucc_le_succ i))
        (by simpa only [sub_zero] using aff i 0 (by simp))
        (aff i Y (by simp [Y]))
end
end HadwigerNelson.Wave

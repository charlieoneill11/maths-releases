import HadwigerNelson.Centres.Parameters
import HadwigerNelson.Forest.Rotations

/-! Angular widths and the unit-disk test for a candidate direction. -/

namespace HadwigerNelson.Centres
noncomputable section
open Placement Set

theorem cone_small (p : Profile) (l : ℝ) : cone p l ≤ 365/100000 := by
  unfold cone
  split
  · exact min_le_left _ _
  · exact (min_le_left _ _).trans (by norm_num)

theorem medium_cone (p : Profile) {l : ℝ} (hl : 2/100<l) : w+cone p l ≤ l/2 := by
  let s := {b : ℝ | b∈mediumBreaks ∧ b<l}
  have mem : (2/100:ℝ) ∈ s := ⟨by simp [mediumBreaks],hl⟩
  have ub := csSup_le (show s.Nonempty from ⟨_,mem⟩) (show ∀ x∈s, x≤l from fun _ h => h.2.le)
  rw [cone,if_neg hl.not_ge]
  change w+min _ (sSup s/2-w) ≤ l/2
  linarith [min_le_right (36/10000:ℝ) (sSup s/2-w)]

theorem cone_half (p : Profile) {l : ℝ} (hl : δR≤l) : cone p l ≤ l/2 := by
  by_cases h : l≤2/100
  · rw [cone,if_pos h]
    apply (min_le_right _ _).trans
    unfold smallLower
    split <;> split <;> first | exact div_le_div_of_nonneg_right hl (by norm_num) | norm_num [δR,δ] at *; grind
  · have := medium_cone p (lt_of_not_ge h)
    linarith [show (0:ℝ)≤w by norm_num [w]]

def verticalStep (s : ℝ) := Wave.point (Real.sin s) (Real.cos s)

theorem step_unit (h : Plane) (s : ℝ) : dist (h-verticalStep s) h = 1 := by
  apply (sq_eq_sq₀ dist_nonneg zero_le_one).mp
  rw [coord_dist_sq]
  simp [verticalStep,Wave.point,Real.sin_sq_add_cos_sq]

theorem unrotate (θ : ℝ) (x : Plane) : rotate θ (rotate (-θ) x)=x := by
  ext i
  fin_cases i <;> simp [rotate,Wave.point] <;>
    first | linear_combination (x 0)*Real.sin_sq_add_cos_sq θ | linear_combination (x 1)*Real.sin_sq_add_cos_sq θ

theorem aligned_diagonal {θ t : ℝ} {u v : Plane} (h : aligned θ t v u) :
    (rotate θ u 0-rotate θ v 0 = dist u v*(-Real.sin t)) ∧
    (rotate θ u 1-rotate θ v 1 = dist u v*Real.cos t) := by
  unfold aligned at h; rw [rotate_sub] at h
  exact ⟨congrArg (fun x : Plane => x 0) h,congrArg (fun x : Plane => x 1) h⟩

theorem downward_distance {θ t : ℝ} {u v : Plane} (h : aligned θ t v u) (s : ℝ) :
    dist (rotate θ u-verticalStep s) (rotate θ v)^2 = 1+(dist u v)^2-2*dist u v*Real.cos (s+t) := by
  obtain ⟨hx,hy⟩ := aligned_diagonal h
  rw [coord_dist_sq,Real.cos_add]
  change (rotate θ u 0-Real.sin s-rotate θ v 0)^2+(rotate θ u 1-Real.cos s-rotate θ v 1)^2=_
  rw [show rotate θ u 0-Real.sin s-rotate θ v 0=(rotate θ u 0-rotate θ v 0)-Real.sin s by ring,
      show rotate θ u 1-Real.cos s-rotate θ v 1=(rotate θ u 1-rotate θ v 1)-Real.cos s by ring,hx,hy]
  linear_combination (dist u v)^2 * Real.sin_sq_add_cos_sq t + Real.sin_sq_add_cos_sq s

theorem aligned_disk_of_sine {θ t s : ℝ} {u v : Plane} (h : aligned θ t v u) (ne : u≠v)
    (D : dist u v ≤ 2) (upper : |Real.sin (s+t)|<chord u v/2) (cs : 0≤Real.cos (s+t)) :
    dist (rotate θ u-verticalStep s) (rotate θ v)<1 := by
  let r := dist u v
  let l := chord u v
  have diag : l^2=4-r^2 := Real.sq_sqrt (by nlinarith [dist_nonneg (x:=u) (y:=v)])
  have hr : 0<r := dist_pos.mpr ne
  change |Real.sin (s+t)|<l/2 at upper
  have low : r/2<Real.cos (s+t) := by
    have strict := (sq_lt_sq₀ (abs_nonneg _) ((abs_nonneg _).trans upper.le)).mpr upper
    rw [sq_abs] at strict
    nlinarith [Real.sin_sq_add_cos_sq (s+t)]
  have d := downward_distance h s
  change _=1+r^2-2*r*_ at d
  nlinarith [mul_lt_mul_of_pos_left low hr, dist_nonneg (x:=rotate θ u-verticalStep s) (y:=rotate θ v)]

theorem aligned_disk {θ t s : ℝ} {u v : Plane} (h : aligned θ t v u) (ne : u≠v)
    (D : dist u v ≤ 2) (hl : 0<chord u v) (width : |s+t|≤chord u v/2) :
    dist (rotate θ u-verticalStep s) (rotate θ v)<1 := by
  let r := dist u v
  let l := chord u v
  have diag : l^2=4-r^2 := Real.sq_sqrt (by nlinarith [dist_nonneg (x:=u) (y:=v)])
  have hr : 0<r := dist_pos.mpr ne
  have L : l≤2 := by nlinarith [sq_nonneg r]
  have upper : |Real.sin (s+t)|<l/2 := by
    by_cases zero : s+t=0
    · simpa [zero,l] using half_pos hl
    · exact (Real.abs_sin_lt_abs zero).trans_le width
  have cs : 0 ≤ Real.cos (s+t) := Real.cos_nonneg_of_mem_Icc ⟨by linarith [(abs_le.mp width).1,Real.two_le_pi],
    by linarith [(abs_le.mp width).2,Real.two_le_pi]⟩
  exact aligned_disk_of_sine h ne D upper cs

end
end HadwigerNelson.Centres

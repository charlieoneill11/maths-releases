import HadwigerNelson.Placement.Coordinates
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.UnitInterval

/-! Parameterization of the consecutive circular arcs used in Lemma 29. -/

namespace HadwigerNelson.Crossings
noncomputable section

def circlePoint (c : Plane) (t : ℝ) : Plane := c+Wave.point (Real.cos t) (Real.sin t)

def circleAngle (c z : Plane) : ℝ := (⟨z 0-c 0,z 1-c 1⟩:ℂ).arg

theorem circlePoint_continuous (c : Plane) : Continuous (circlePoint c) :=
  continuous_const.add (Placement.continuous_point Real.continuous_cos Real.continuous_sin)

theorem circleAngle_bounds (c z : Plane) : circleAngle c z ∈ Set.Ioc (-Real.pi) Real.pi :=
  Complex.arg_mem_Ioc _

theorem dist_circlePoint (c : Plane) (t : ℝ) : dist (circlePoint c t) c = 1 := by
  have h : dist (circlePoint c t) c ^ 2 = 1 := by
    rw [EuclideanSpace.dist_sq_eq,Fin.sum_univ_two]
    simp [circlePoint,Wave.point,sq_abs,Real.cos_sq_add_sin_sq]
  nlinarith [show 0 ≤ dist (circlePoint c t) c from dist_nonneg]

theorem circlePoint_angle {c z : Plane} (h : dist z c = 1) :
    circlePoint c (circleAngle c z) = z := by
  let w : ℂ := ⟨z 0-c 0,z 1-c 1⟩
  have he := EuclideanSpace.dist_sq_eq z c
  rw [h,Fin.sum_univ_two] at he
  have hw : ‖w‖ = 1 := by
    rw [Complex.norm_def,Complex.normSq_mk]
    have : (z 0-c 0)*(z 0-c 0)+(z 1-c 1)*(z 1-c 1) = 1 := by
      simpa [Real.dist_eq,sq_abs,sq] using he.symm
    rw [this,Real.sqrt_one]
  have hc : Real.cos w.arg = z 0-c 0 := by simpa [hw,w] using Complex.norm_mul_cos_arg w
  have hs : Real.sin w.arg = z 1-c 1 := by simpa [hw,w] using Complex.norm_mul_sin_arg w
  ext i
  fin_cases i <;> simp [circlePoint,circleAngle,Wave.point,w] at hc hs ⊢ <;> linarith

theorem circlePoint_add_period (c : Plane) (t : ℝ) :
    circlePoint c (t+2*Real.pi) = circlePoint c t := by
  simp [circlePoint,Real.cos_add_two_pi,Real.sin_add_two_pi]

theorem circlePoint_inj_of_short {c : Plane} {s t : ℝ}
    (hlo : -(2*Real.pi) < s-t) (hhi : s-t < 2*Real.pi)
    (h : circlePoint c s = circlePoint c t) : s = t := by
  have hs := congrArg (fun p : Plane => p 1) h
  have hc := congrArg (fun p : Plane => p 0) h
  simp [circlePoint,Wave.point] at hs hc
  have ec : Circle.exp s = Circle.exp t := by
    apply Subtype.ext
    change Complex.exp ((s:ℂ)*Complex.I) = Complex.exp ((t:ℂ)*Complex.I)
    apply Complex.ext <;> simp [hs,hc]
  obtain ⟨m,hm⟩ := Circle.exp_eq_exp.mp ec
  have hp : 0 < 2*Real.pi := by positivity
  rcases lt_trichotomy m 0 with hm'|rfl|hm'
  · have hm1 : (m:ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
    linarith [mul_le_mul_of_nonneg_right hm1 hp.le]
  · simpa using hm
  · have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    linarith [mul_le_mul_of_nonneg_right hm1 hp.le]

def arcAngle (a b : ℝ) (t : unitInterval) : ℝ := a+(b-a)*(t:ℝ)

theorem arcAngle_mem (a b : ℝ) (hab : a < b) (t : unitInterval) :
    arcAngle a b t ∈ Set.Icc a b := by
  dsimp [arcAngle]
  exact ⟨by nlinarith [mul_nonneg (sub_nonneg.mpr hab.le) t.2.1],
    by nlinarith [mul_nonneg (sub_nonneg.mpr hab.le) (sub_nonneg.mpr t.2.2)]⟩

theorem arcAngle_mem_interior (a b : ℝ) (hab : a < b) {t : unitInterval}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) : arcAngle a b t ∈ Set.Ioo a b := by
  have h0 : 0 < (t:ℝ) := lt_of_le_of_ne t.2.1 fun h => ht0 (Subtype.ext h.symm)
  have h1 : (t:ℝ) < 1 := lt_of_le_of_ne t.2.2 fun h => ht1 (Subtype.ext h)
  dsimp [arcAngle]
  exact ⟨by nlinarith [mul_pos (sub_pos.mpr hab) h0],
    by nlinarith [mul_pos (sub_pos.mpr hab) (sub_pos.mpr h1)]⟩

def circleArc (c : Plane) (a b : ℝ) (t : unitInterval) := circlePoint c (arcAngle a b t)

theorem circleArc_continuous (c : Plane) (a b : ℝ) : Continuous (circleArc c a b) :=
  (circlePoint_continuous c).comp (continuous_const.add (continuous_const.mul continuous_subtype_val))

theorem circleArc_injective (c : Plane) {a b : ℝ} (hab : a < b) (hlen : b-a < 2*Real.pi) :
    Function.Injective (circleArc c a b) := by
  intro t u h
  have ht := arcAngle_mem a b hab t
  have hu := arcAngle_mem a b hab u
  have eqn := circlePoint_inj_of_short (s := arcAngle a b t) (t := arcAngle a b u)
    (by linarith [ht.1,hu.2]) (by linarith [ht.2,hu.1]) h
  apply Subtype.ext
  exact (mul_left_cancel₀ (sub_pos.mpr hab).ne') (add_left_cancel eqn)

@[simp] theorem circleArc_zero (c : Plane) (a b : ℝ) : circleArc c a b 0 = circlePoint c a := by
  simp [circleArc,arcAngle]
@[simp] theorem circleArc_one (c : Plane) (a b : ℝ) : circleArc c a b 1 = circlePoint c b := by
  simp [circleArc,arcAngle]

end
end HadwigerNelson.Crossings

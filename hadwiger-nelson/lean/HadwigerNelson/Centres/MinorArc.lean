import HadwigerNelson.Blueprint.Point.Rhombus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! The angle and projection tests for the interior of the minor arc of
a unit rhombus, including the endpoints of the containing semicircle. -/

namespace HadwigerNelson.Centres
noncomputable section

def chord (u v : Plane) : ℝ := Real.sqrt (4-dist u v^2)
def midpoint (u v : Plane) : Plane := (1/2:ℝ) • (u+v)

def inMinorInterior (p q u v z : Plane) : Prop :=
  dist z u = 1 ∧ 0 ≤ inner ℝ (z-u) (v-u) ∧
    |inner ℝ (z-midpoint p q) (q-p)| < dist p q^2/2

/-- The determinant of the Gram matrix of three planar vectors vanishes. -/
private theorem plane_gram (a b c : Plane) :
    (inner ℝ a b)^2*‖c‖^2+(inner ℝ a c)^2*‖b‖^2+(inner ℝ b c)^2*‖a‖^2 =
      ‖a‖^2*‖b‖^2*‖c‖^2+2*inner ℝ a b*inner ℝ a c*inner ℝ b c := by
  have dot (x y : Plane) : inner ℝ x y = x 0*y 0+x 1*y 1 := by
    rw [PiLp.inner_apply,Fin.sum_univ_two]
    change y 0*x 0+y 1*x 1 = _
    ring
  simp only [← real_inner_self_eq_norm_sq,dot]
  ring

theorem minor_arc_criterion (p q u v z : Plane) (hpq : p ≠ q) (huv : u ≠ v)
    (hup : dist u p = 1) (huq : dist u q = 1) (hvp : dist v p = 1) (hvq : dist v q = 1)
    (hz : dist z u = 1) (hs : 0 ≤ inner ℝ (z-u) (v-u)) :
    (Real.arccos (inner ℝ (z-u) (v-u) / dist v u) < Real.arcsin (dist p q/2)) ↔
      inMinorInterior p q u v z := by
  obtain ⟨hm,_,perp⟩ := rhombus_geometry p q u v hpq huv hup huq hvp hvq
  have orth : inner ℝ (v-u) (q-p) = 0 := by rw [← neg_sub u v, inner_neg_left,perp,neg_zero]
  have mid : z-midpoint p q = (z-u)+(1/2:ℝ) • (u-v) := by
    rw [midpoint,hm]; ext i; simp; ring
  have projection : inner ℝ (z-midpoint p q) (q-p) = inner ℝ (z-u) (q-p) := by
    rw [mid,inner_add_left,real_inner_smul_left,perp,mul_zero,add_zero]
  let P := inner ℝ (z-u) (v-u)
  let Q := inner ℝ (z-u) (q-p)
  let r := dist v u
  let l := dist p q
  have hr : 0<r := dist_pos.mpr huv.symm
  have hl : 0<l := dist_pos.mpr hpq
  have h₂ : l≤2 := by
    have h := dist_triangle p u q
    rw [dist_comm p u,hup,huq] at h
    dsimp [l]; linarith
  have hP : 0≤P/r := div_nonneg hs hr.le
  have gram := plane_gram (z-u) (v-u) (q-p)
  rw [← dist_eq_norm,← dist_eq_norm,← dist_eq_norm,dist_comm q p,hz,orth] at gram
  change P^2*l^2+Q^2*r^2+0^2*1^2=1^2*r^2*l^2+2*P*Q*0 at gram
  have proj : (P/r)^2+(Q/l)^2=1 := by
    field_simp [hr.ne',hl.ne']
    nlinarith only [gram]
  have hq : |Q/l|≤1 := by nlinarith [sq_abs (Q/l),sq_nonneg (P/r)]
  have sqr : Real.sqrt (1-(P/r)^2) = |Q/l| := by
    rw [show 1-(P/r)^2=(Q/l)^2 by linarith [proj],Real.sqrt_sq_eq_abs]
  change Real.arccos (P/r) < Real.arcsin (l/2) ↔ _
  rw [Real.arccos_eq_arcsin hP,sqr,Real.strictMonoOn_arcsin.lt_iff_lt
    (show |Q/l| ∈ Set.Icc (-1:ℝ) 1 from ⟨by linarith [abs_nonneg (Q/l)],hq⟩)
    (show l/2 ∈ Set.Icc (-1:ℝ) 1 from ⟨by linarith, by linarith⟩)]
  rw [inMinorInterior,projection,abs_div,abs_of_pos hl,div_lt_iff₀ hl]
  change |Q| < l/2*l ↔ _
  simp only [hz,hs,true_and]
  change |Q| < l/2*l ↔ |Q| < l^2/2
  ring_nf

end
end HadwigerNelson.Centres

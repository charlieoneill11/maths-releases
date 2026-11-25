import HadwigerNelson.Crossings.CircleKnots
import HadwigerNelson.Forest.Rotations
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace HadwigerNelson.Packing
open Finset Crossings
noncomputable section

/-- Polar coordinates give the squared-distance formula in the signed Euclidean plane. -/
theorem polar_distance (c x y : Plane) : dist x y ^ 2 = dist x c ^ 2 + dist y c ^ 2 -
    2 * dist x c * dist y c * Real.cos (circleAngle c y-circleAngle c x) := by
  let w (z : Plane) : ℂ := ⟨z 0-c 0,z 1-c 1⟩
  have norm (z : Plane) : ‖w z‖ = dist z c := by
    apply (sq_eq_sq₀ (norm_nonneg _) dist_nonneg).mp
    rw [Complex.sq_norm,Placement.coord_dist_sq,Complex.normSq_mk]; ring
  have xc (z : Plane) : dist z c*Real.cos (circleAngle c z) = z 0-c 0 := by
    simpa only [←norm,w,circleAngle] using Complex.norm_mul_cos_arg (w z)
  have ys (z : Plane) : dist z c*Real.sin (circleAngle c z) = z 1-c 1 := by
    simpa only [←norm,w,circleAngle] using Complex.norm_mul_sin_arg (w z)
  rw [Placement.coord_dist_sq,Real.cos_sub]
  linear_combination (Placement.coord_dist_sq x c).symm + (Placement.coord_dist_sq y c).symm +
    2 * (dist y c * Real.cos (circleAngle c y)) * xc x +
    2 * (x 0-c 0) * xc y + 2 * (dist y c * Real.sin (circleAngle c y)) * ys x +
    2 * (x 1-c 1) * ys y

/-- Some pair of distinct points has angular separation at most a full turn divided by
the number of points. Points on the same ray are allowed, including a repeated angle. -/
theorem angular_gap (P : Finset Plane) (c : Plane) (hP : 2 ≤ P.card) :
    ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ ∃ g, 0 ≤ g ∧ g ≤ 2*Real.pi/P.card ∧
      Real.cos g = Real.cos (circleAngle c y - circleAngle c x) := by
  classical
  let θ := circleAngle c
  by_cases inj : Set.InjOn θ P
  · let Q := P.image θ
    have card : Q.card=P.card := Finset.card_image_of_injOn inj
    let t := Q.orderEmbOfFin card
    have pos : 0 < P.card := by omega
    let first : Fin P.card := ⟨0,pos⟩
    let s (i : ℕ) := if h : i<P.card then t ⟨i,h⟩ else t first+2*Real.pi
    have tot : ∑ i ∈ Finset.range P.card, (s (i+1)-s i) = 2*Real.pi := by
      rw [Finset.sum_range_sub]; simp [s,pos,first]
    have small : ∃ i < P.card, s (i+1)-s i ≤ 2*Real.pi/P.card := by
      by_contra! big
      have lt := Finset.sum_lt_sum (s:=Finset.range P.card) (fun i hi ↦ (big i (mem_range.mp hi)).le)
        ⟨0,mem_range.mpr pos,big 0 pos⟩
      rw [tot,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at lt
      have hp : (P.card:ℝ) ≠ 0 := by exact_mod_cast pos.ne'
      field_simp [hp] at lt
      linarith
    obtain ⟨i,hi,hg⟩ := small
    let a : Fin P.card := ⟨i,hi⟩
    let b := CircleKnots.next a
    obtain ⟨x,hx,ex⟩ := Finset.mem_image.mp (Q.orderEmbOfFin_mem card a)
    obtain ⟨y,hy,ey⟩ := Finset.mem_image.mp (Q.orderEmbOfFin_mem card b)
    have hne : x ≠ y := fun h ↦ (CircleKnots.next_ne hP a) (t.injective (ey.symm.trans ((congrArg θ h.symm).trans ex)))
    refine ⟨x,hx,y,hy,hne,s (i+1)-s i,?_,hg,?_⟩
    · have hb : ∀ j, t j ∈ Set.Ioc (-Real.pi) Real.pi := by
        intro j
        obtain ⟨z,_,e⟩ := Finset.mem_image.mp (Q.orderEmbOfFin_mem card j)
        exact e ▸ circleAngle_bounds c z
      by_cases is : i+1<P.card
      · simp only [s,dif_pos hi,dif_pos is,sub_nonneg]
        exact t.monotone (by change i ≤ i+1; omega)
      · simp only [s,dif_pos hi,dif_neg is,sub_nonneg]
        linarith [(hb first).1,(hb a).2]
    · change Real.cos _ = Real.cos (θ y-θ x)
      change θ x = t a at ex
      change θ y = t b at ey
      rw [ex,ey]
      by_cases is : i+1<P.card
      · simp [s,b,a,CircleKnots.next,is,hi]
      · have eb : b = first := by simp [b,a,CircleKnots.next,CircleKnots.first,is,first]
        rw [eb]
        simp only [s,dif_pos hi,dif_neg is]
        rw [show t first+2*Real.pi-t a = (t first-t a)+2*Real.pi by ring,Real.cos_add_two_pi]
  · simp only [Set.InjOn] at inj
    push Not at inj
    obtain ⟨x,hx,y,hy,same,ne⟩ := inj
    refine ⟨x,hx,y,hy,ne,0,le_rfl,by positivity,?_⟩
    change Real.cos 0 = Real.cos (θ y-θ x)
    rw [same,sub_self]

end
end HadwigerNelson.Packing

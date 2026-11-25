import HadwigerNelson.Crossings.UnitDegrees
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace HadwigerNelson.Crossings
noncomputable section

/-- The two disjoint exceptional classes receive weights α and β. -/
def weightedBound (n : ℕ) (m s j α β : ℝ) : ℝ :=
  2 * m / n * (α * s + β * j) +
    Real.sqrt (2 * varianceBound n 2090 m * (α ^ 2 * s + β ^ 2 * j - (α * s + β * j) ^ 2 / n))

/-- Centre both degree and weight before applying the finite Cauchy–Schwarz
inequality. Disjointness makes the second moment of the weights additive. -/
theorem weighted_of_variance (X S J : Finset Plane) (α β : ℝ)
    (hn : 0<X.card) (hS : S ⊆ X) (hJ : J ⊆ X) (dis : Disjoint S J)
    (variance : (∑ x ∈ X, ((unitDegree X x : ℝ) - 2*(unitEdgeCount X : ℝ)/X.card)^2) ≤
      2*varianceBound X.card 2090 (unitEdgeCount X)) :
    α * (∑ x ∈ S, (unitDegree X x : ℝ)) + β * (∑ x ∈ J, (unitDegree X x : ℝ)) ≤
      weightedBound X.card (unitEdgeCount X) S.card J.card α β := by
  classical
  let D (x : Plane) : ℝ := unitDegree X x
  let μ : ℝ := 2*(unitEdgeCount X : ℝ)/X.card
  let w (x : Plane) : ℝ := (if x∈S then α else 0)+(if x∈J then β else 0)
  let T : ℝ := α*S.card+β*J.card
  let t : ℝ := T/X.card
  have npos : (0:ℝ)<X.card := by exact_mod_cast hn
  have eval (f : Plane → ℝ) : ∑ x ∈ X, w x * f x = α * (∑ x ∈ S, f x) + β * (∑ x ∈ J, f x) := by
    simp only [w,add_mul,ite_mul,zero_mul,Finset.sum_add_distrib,Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr hS,Finset.inter_eq_right.mpr hJ,Finset.mul_sum]
  have total : ∑ x ∈ X, w x = T := by
    simpa [T] using eval (fun _ => 1)
  have moment : ∑ x ∈ X, (w x)^2 = α^2*S.card+β^2*J.card := by
    calc
      _ = ∑ x ∈ X, ((if x∈S then α^2 else 0)+(if x∈J then β^2 else 0)) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases a : x∈S
        · have b := Finset.disjoint_left.mp dis a
          simp [w,a,b]
        · by_cases b : x∈J <;> simp [w,a,b]
      _ = _ := by
        simp only [Finset.sum_add_distrib,Finset.sum_ite_mem,Finset.inter_eq_right.mpr hS,
          Finset.inter_eq_right.mpr hJ,Finset.sum_const,nsmul_eq_mul]
        ring
  have degTotal : ∑ x ∈ X, D x = 2*(unitEdgeCount X : ℝ) := by
    simpa only [D,← Nat.cast_sum,Nat.cast_mul,Nat.cast_ofNat] using
      congrArg (fun v : ℕ => (v:ℝ)) (sum_unitDegree X)
  have centered : ∑ x ∈ X, (D x - μ) = 0 := by
    rw [Finset.sum_sub_distrib, degTotal, Finset.sum_const, nsmul_eq_mul]
    dsimp only [μ]
    field_simp
    ring
  have wSq : ∑ x ∈ X, (w x - t)^2 = α^2*S.card+β^2*J.card-T^2/X.card := by
    simp_rw [sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.sum_mul,
      ←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,total,moment]
    dsimp only [t]
    field_simp
    ring
  have cov : ∑ x ∈ X, (D x-μ)*(w x-t) =
      α*(∑ x ∈ S, D x)+β*(∑ x ∈ J, D x)-μ*T := by
    have step (x : Plane) : (D x-μ)*(w x-t) = (w x*D x-μ*w x) - (D x-μ)*t := by ring
    simp_rw [step,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.sum_mul,centered,total,eval D]
    ring
  have C := Finset.sum_mul_sq_le_sq_mul_sq X (fun x => D x-μ) (fun x => w x-t)
  have bound := C.trans (mul_le_mul_of_nonneg_right variance (Finset.sum_nonneg fun x _ => sq_nonneg (w x-t)))
  rw [cov,wSq] at bound
  have h := Real.le_sqrt_of_sq_le bound
  change α*(∑ x ∈ S, D x)+β*(∑ x ∈ J, D x) ≤ μ*T + _
  linarith only [h]

end
end HadwigerNelson.Crossings

import Chowla.VariationalMoments

namespace Chowla

open MvPolynomial
open scoped BigOperators

namespace MomentPolynomial

noncomputable def eval {R : Type*} [CommSemiring R] (coeff : ℝ →+* R) (atom : MomentTest → R)
    (P : MomentPolynomial) : R :=
  (P.map fun t => coeff t.1 * (t.2.map atom).prod).sum

noncomputable def mul (P Q : MomentPolynomial) : MomentPolynomial :=
  P.flatMap fun s => Q.map fun t => (s.1 * t.1, s.2 ++ t.2)

noncomputable def const (c : ℝ) : MomentPolynomial := [(c, [])]

noncomputable def atom (f : MomentTest) : MomentPolynomial := [(1, [f])]

noncomputable def prod (L : List MomentPolynomial) : MomentPolynomial :=
  L.foldr mul (const 1)

noncomputable def sum (L : List MomentPolynomial) : MomentPolynomial := L.flatten

theorem eval_append {R : Type*} [CommSemiring R] (coeff : ℝ →+* R) (x : MomentTest → R)
    (P Q : MomentPolynomial) : eval coeff x (P ++ Q) = eval coeff x P + eval coeff x Q := by
  simp [eval]

@[simp] theorem eval_const {R : Type*} [CommSemiring R] (coeff : ℝ →+* R) (x : MomentTest → R)
    (c : ℝ) : eval coeff x (const c) = coeff c := by simp [eval, const]

@[simp] theorem eval_atom {R : Type*} [CommSemiring R] (coeff : ℝ →+* R) (x : MomentTest → R)
    (f : MomentTest) : eval coeff x (atom f) = x f := by simp [eval, atom]

private theorem eval_single_mul {R : Type*} [CommSemiring R] (coeff : ℝ →+* R) (x : MomentTest → R)
    (s : ℝ × List MomentTest) (Q : MomentPolynomial) :
    eval coeff x (Q.map fun t => (s.1 * t.1, s.2 ++ t.2)) =
      (coeff s.1 * (s.2.map x).prod) * eval coeff x Q := by
  induction Q with
  | nil => simp [eval]
  | cons t ts ih =>
      simp only [List.map_cons, eval, List.sum_cons, map_mul, List.map_append, List.prod_append] at ih ⊢
      rw [ih, mul_add]
      ring

@[simp] theorem eval_mul {R : Type*} [CommSemiring R] (coeff : ℝ →+* R) (x : MomentTest → R)
    (P Q : MomentPolynomial) : eval coeff x (mul P Q) = eval coeff x P * eval coeff x Q := by
  induction P with
  | nil => simp [mul, eval]
  | cons s ss ih =>
      rw [show mul (s :: ss) Q = (Q.map fun t => (s.1 * t.1, s.2 ++ t.2)) ++ mul ss Q from rfl]
      rw [eval_append, eval_single_mul, ih, show eval coeff x (s :: ss) =
        coeff s.1 * (s.2.map x).prod + eval coeff x ss from rfl, add_mul]

@[simp] theorem eval_prod {R : Type*} [CommSemiring R] (coeff : ℝ →+* R) (x : MomentTest → R)
    (L : List MomentPolynomial) : eval coeff x (prod L) = (L.map (eval coeff x)).prod := by
  induction L with
  | nil => simp [prod]
  | cons P L ih => simp [prod, ← ih]

@[simp] theorem eval_sum {R : Type*} [CommSemiring R] (coeff : ℝ →+* R) (x : MomentTest → R)
    (L : List MomentPolynomial) : eval coeff x (sum L) = (L.map (eval coeff x)).sum := by
  induction L with
  | nil => simp [sum, eval]
  | cons P L ih => simp [sum, eval_append, ← ih]

theorem eval_real (P : MomentPolynomial) (X : ℝ) (d : ℤ) :
    eval (RingHom.id ℝ) (fun f => zeroStatistic (fun x => f.toSchwartz x) d X) P =
      P.statistic X d := rfl

theorem eval_model (P : MomentPolynomial) : eval C (fun f => stat f.profile) P = P.model := rfl

theorem bandwidth_append (L R : List MomentTest) :
    MomentWord.bandwidth (L ++ R) = MomentWord.bandwidth L + MomentWord.bandwidth R := by
  simp [MomentWord.bandwidth]

theorem mem_mul {P Q : MomentPolynomial} {t : ℝ × List MomentTest} (ht : t ∈ mul P Q) :
    ∃ s ∈ P, ∃ u ∈ Q, t = (s.1 * u.1, s.2 ++ u.2) := by
  obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨u, hu, heq⟩ := List.mem_map.mp ht
  exact ⟨s, hs, u, hu, heq.symm⟩

theorem bandwidth_mul {P Q : MomentPolynomial} {b c : ℝ}
    (hP : ∀ t ∈ P, MomentWord.bandwidth t.2 ≤ b)
    (hQ : ∀ t ∈ Q, MomentWord.bandwidth t.2 ≤ c) :
    ∀ t ∈ mul P Q, MomentWord.bandwidth t.2 ≤ b + c := by
  intro t ht
  obtain ⟨s, hs, u, hu, rfl⟩ := mem_mul ht
  rw [bandwidth_append]
  exact add_le_add (hP s hs) (hQ u hu)

theorem bandwidth_prod {α : Type*} (L : List α) (P : α → MomentPolynomial) (b : α → ℝ)
    (h : ∀ v ∈ L, ∀ t ∈ P v, MomentWord.bandwidth t.2 ≤ b v) :
    ∀ t ∈ prod (L.map P), MomentWord.bandwidth t.2 ≤ (L.map b).sum := by
  induction L with
  | nil => simp [prod, const, MomentWord.bandwidth]
  | cons a as ih =>
      exact bandwidth_mul (h a (List.mem_cons_self ..))
        (ih (fun v hv => h v (List.mem_cons_of_mem _ hv)))

end MomentPolynomial

end Chowla

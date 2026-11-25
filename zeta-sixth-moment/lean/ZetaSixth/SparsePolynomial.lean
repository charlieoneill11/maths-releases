import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Tactic.Ring

/-!
# Sparse polynomials for exact cell integration

A polynomial is a list of terms with rational coefficients. Arithmetic combines repeated
powers, and definite integration substitutes the two polynomial endpoints into the
primitive. Evaluation and integration soundness are independent of the representation's
ordering.
-/

namespace ZetaSixth

/-- Which variable to substitute or integrate. -/
inductive Axis where
  | first
  | second
  | third

namespace Axis

/-- Replace one coordinate, leaving the others fixed. -/
def replace {K : Type*} : Axis → K × K × K → K → K × K × K
  | .first, p, t => (t, p.2.1, p.2.2)
  | .second, p, t => (p.1, t, p.2.2)
  | .third, p, t => (p.1, p.2.1, t)

end Axis

/-- Powers of the three variables in a monomial. -/
structure Powers where
  first : ℕ
  second : ℕ
  third : ℕ
  deriving DecidableEq

namespace Powers

def get (e : Powers) : Axis → ℕ
  | .first => e.first
  | .second => e.second
  | .third => e.third

def set (e : Powers) : Axis → ℕ → Powers
  | .first, n => { e with first := n }
  | .second, n => { e with second := n }
  | .third, n => { e with third := n }

def add (e f : Powers) : Powers :=
  ⟨e.first + f.first, e.second + f.second, e.third + f.third⟩

def eval {K : Type*} [Field K] (e : Powers) (p : K × K × K) : K :=
  p.1 ^ e.first * p.2.1 ^ e.second * p.2.2 ^ e.third

theorem eval_add {K : Type*} [Field K] (e f : Powers) (p : K × K × K) :
    (e.add f).eval p = e.eval p * f.eval p := by
  simp only [eval, add, pow_add]
  ring

theorem eval_replace {K : Type*} [Field K] (e : Powers) (a : Axis) (p : K × K × K) (t : K) :
    e.eval (a.replace p t) = (e.set a 0).eval p * t ^ e.get a := by
  cases a <;> simp only [eval, get, set, Axis.replace, pow_zero, one_mul, mul_one] <;> ring

theorem eval_set_replace {K : Type*} [Field K] (e : Powers) (a : Axis)
    (p : K × K × K) (t : K) (n : ℕ) :
    (e.set a n).eval (a.replace p t) = (e.set a 0).eval p * t ^ n := by
  cases a <;> simp only [eval, set, Axis.replace, pow_zero, one_mul, mul_one] <;> ring

end Powers

/-- One term of a sparse polynomial. -/
structure SparseTerm where
  coeff : ℚ
  powers : Powers

namespace SparseTerm

def eval {K : Type*} [Field K] (t : SparseTerm) (p : K × K × K) : K :=
  (t.coeff : K) * t.powers.eval p

def mul (s t : SparseTerm) : SparseTerm := ⟨s.coeff * t.coeff, s.powers.add t.powers⟩

theorem eval_mul {K : Type*} [Field K] [CharZero K] (s t : SparseTerm) (p : K × K × K) :
    (s.mul t).eval p = s.eval p * t.eval p := by
  simp only [eval, mul, Rat.cast_mul, Powers.eval_add]
  ring

def primitive (t : SparseTerm) (a : Axis) : SparseTerm :=
  let n := t.powers.get a + 1
  ⟨t.coeff / (n : ℚ), t.powers.set a n⟩

end SparseTerm

/-- A list of monomials with rational coefficients. -/
abbrev SparsePoly := List SparseTerm

namespace SparsePoly

def eval {K : Type*} [Field K] (p : SparsePoly) (q : K × K × K) : K :=
  match p with
  | [] => 0
  | t :: ts => t.eval q + eval ts q

@[simp] theorem eval_nil {K : Type*} [Field K] (q : K × K × K) :
    eval [] q = 0 := rfl

@[simp] theorem eval_cons {K : Type*} [Field K] (t : SparseTerm) (ts : SparsePoly)
    (q : K × K × K) : eval (t :: ts) q = t.eval q + eval ts q := rfl

@[simp] theorem eval_append {K : Type*} [Field K] (p r : SparsePoly) (q : K × K × K) :
    eval (p ++ r) q = eval p q + eval r q := by
  induction p with
  | nil => simp
  | cons t ts ih => simp [ih, add_assoc]

/-- Insert one term and merge it with the first term of the same powers. -/
def insertTerm (t : SparseTerm) : SparsePoly → SparsePoly
  | [] => [t]
  | s :: ss =>
    if t.powers = s.powers then
      if t.coeff + s.coeff = 0 then ss else ⟨t.coeff + s.coeff, s.powers⟩ :: ss
    else s :: insertTerm t ss

theorem eval_insertTerm {K : Type*} [Field K] [CharZero K]
    (t : SparseTerm) (p : SparsePoly) (q : K × K × K) :
    eval (insertTerm t p) q = t.eval q + eval p q := by
  induction p with
  | nil => simp [insertTerm]
  | cons s ss ih =>
    by_cases hp : t.powers = s.powers
    · by_cases hz : t.coeff + s.coeff = 0
      · simp only [insertTerm, hp, if_true, if_pos hz, eval_cons, SparseTerm.eval]
        have hcast : (t.coeff : K) + (s.coeff : K) = 0 := by
          rw [← Rat.cast_add, hz, Rat.cast_zero]
        rw [← add_assoc, ← add_mul, hcast, zero_mul, zero_add]
      · simp only [insertTerm, hp, if_true, if_neg hz, eval_cons, SparseTerm.eval, Rat.cast_add]
        ring
    · simp [insertTerm, hp, ih, add_left_comm]

def compact : SparsePoly → SparsePoly
  | [] => []
  | t :: ts => insertTerm t (compact ts)

@[simp] theorem eval_compact {K : Type*} [Field K] [CharZero K] (p : SparsePoly)
    (q : K × K × K) : eval (compact p) q = eval p q := by
  induction p with
  | nil => rfl
  | cons t ts ih => simp [compact, eval_insertTerm, ih]

def const (r : ℚ) : SparsePoly := [⟨r, ⟨0, 0, 0⟩⟩]

def variablePoly (a : Axis) : SparsePoly := [⟨1, (⟨0, 0, 0⟩ : Powers).set a 1⟩]

@[simp] theorem eval_const {K : Type*} [Field K] (r : ℚ) (q : K × K × K) :
    eval (const r) q = (r : K) := by simp [const, SparseTerm.eval, Powers.eval]

@[simp] theorem eval_variable_first {K : Type*} [Field K] (q : K × K × K) :
    eval (variablePoly .first) q = q.1 := by
  simp [variablePoly, Powers.set, SparseTerm.eval, Powers.eval]

@[simp] theorem eval_variable_second {K : Type*} [Field K] (q : K × K × K) :
    eval (variablePoly .second) q = q.2.1 := by
  simp [variablePoly, Powers.set, SparseTerm.eval, Powers.eval]

@[simp] theorem eval_variable_third {K : Type*} [Field K] (q : K × K × K) :
    eval (variablePoly .third) q = q.2.2 := by
  simp [variablePoly, Powers.set, SparseTerm.eval, Powers.eval]

def add (p r : SparsePoly) : SparsePoly := compact (p ++ r)

def neg (p : SparsePoly) : SparsePoly := p.map fun t => { t with coeff := -t.coeff }

def sub (p r : SparsePoly) : SparsePoly := add p (neg r)

def mul (p r : SparsePoly) : SparsePoly := compact (p.flatMap fun t => r.map (t.mul ·))

def pow (p : SparsePoly) : ℕ → SparsePoly
  | 0 => const 1
  | n + 1 => mul (pow p n) p

@[simp] theorem eval_add {K : Type*} [Field K] [CharZero K] (p r : SparsePoly)
    (q : K × K × K) : eval (add p r) q = eval p q + eval r q := by
  simp [add]

@[simp] theorem eval_neg {K : Type*} [Field K] [CharZero K] (p : SparsePoly)
    (q : K × K × K) : eval (neg p) q = -eval p q := by
  induction p with
  | nil => simp [neg]
  | cons t ts ih =>
    simp only [neg, List.map_cons, eval_cons, SparseTerm.eval, Rat.cast_neg, neg_mul] at ih ⊢
    rw [ih, neg_add]

@[simp] theorem eval_sub {K : Type*} [Field K] [CharZero K] (p r : SparsePoly)
    (q : K × K × K) : eval (sub p r) q = eval p q - eval r q := by
  simp [sub, sub_eq_add_neg]

private theorem eval_map_mul {K : Type*} [Field K] [CharZero K] (t : SparseTerm)
    (r : SparsePoly) (q : K × K × K) :
    eval (r.map (t.mul ·)) q = t.eval q * eval r q := by
  induction r with
  | nil => simp
  | cons s ss ih => simp [SparseTerm.eval_mul, ih, mul_add]

private theorem eval_flatMap_mul {K : Type*} [Field K] [CharZero K] (p r : SparsePoly)
    (q : K × K × K) :
    eval (p.flatMap fun t => r.map (t.mul ·)) q = eval p q * eval r q := by
  induction p with
  | nil => simp
  | cons t ts ih => simp [eval_map_mul, ih, add_mul]

@[simp] theorem eval_mul {K : Type*} [Field K] [CharZero K] (p r : SparsePoly)
    (q : K × K × K) : eval (mul p r) q = eval p q * eval r q := by
  simp [mul, eval_flatMap_mul]

@[simp] theorem eval_pow {K : Type*} [Field K] [CharZero K] (p : SparsePoly)
    (n : ℕ) (q : K × K × K) : eval (pow p n) q = eval p q ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow, pow_succ, ih]

def substitute (a : Axis) (r : SparsePoly) : SparsePoly → SparsePoly
  | [] => []
  | t :: ts =>
    add (mul [⟨t.coeff, t.powers.set a 0⟩] (pow r (t.powers.get a)))
      (substitute a r ts)

@[simp] theorem eval_substitute {K : Type*} [Field K] [CharZero K] (p r : SparsePoly)
    (a : Axis) (q : K × K × K) : eval (substitute a r p) q = eval p (a.replace q (eval r q)) := by
  induction p with
  | nil => rfl
  | cons t ts ih =>
    simp only [substitute, eval_add, eval_mul, eval_cons, eval_nil, add_zero, eval_pow,
      ih, SparseTerm.eval, Powers.eval_replace, mul_assoc]

def primitive (a : Axis) (p : SparsePoly) : SparsePoly := p.map (·.primitive a)

def integrate (p : SparsePoly) (a : Axis) (lo hi : SparsePoly) : SparsePoly :=
  sub (substitute a hi (primitive a p)) (substitute a lo (primitive a p))

theorem eval_ratCast (p : SparsePoly) (q : ℚ × ℚ × ℚ) :
    ((eval p q : ℚ) : ℝ) = eval p ((q.1 : ℝ), (q.2.1 : ℝ), (q.2.2 : ℝ)) := by
  induction p with
  | nil => simp
  | cons t ts ih =>
    simp [SparseTerm.eval, Powers.eval, Rat.cast_pow, Rat.cast_mul, Rat.cast_add, ih]

theorem continuous_eval (p : SparsePoly) : Continuous (fun q : ℝ × ℝ × ℝ => eval p q) := by
  induction p with
  | nil => simp [continuous_const]
  | cons t ts ih =>
    simp only [eval_cons, SparseTerm.eval, Powers.eval]
    exact (continuous_const.mul (((continuous_fst.pow _).mul
      ((continuous_fst.comp continuous_snd).pow _)).mul
      ((continuous_snd.comp continuous_snd).pow _))).add ih

private theorem continuous_eval_replace (p : SparsePoly) (a : Axis) (q : ℝ × ℝ × ℝ) :
    Continuous (fun t : ℝ => eval p (a.replace q t)) := by
  have h : Continuous (fun t : ℝ => a.replace q t) := by
    cases a
    · exact continuous_id.prodMk (continuous_const.prodMk continuous_const)
    · exact continuous_const.prodMk (continuous_id.prodMk continuous_const)
    · exact continuous_const.prodMk (continuous_const.prodMk continuous_id)
  exact p.continuous_eval.comp h

private theorem eval_term_primitive_sub (t : SparseTerm) (a : Axis) (q : ℝ × ℝ × ℝ)
    (lo hi : ℝ) :
    (t.primitive a).eval (a.replace q hi) - (t.primitive a).eval (a.replace q lo) =
      ∫ s in lo..hi, t.eval (a.replace q s) := by
  simp only [SparseTerm.eval, SparseTerm.primitive, Rat.cast_div, Rat.cast_natCast]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Powers.eval_set_replace, Powers.eval_set_replace]
  simp_rw [Powers.eval_replace, ← mul_assoc]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  ring

theorem eval_primitive_sub (p : SparsePoly) (a : Axis) (q : ℝ × ℝ × ℝ) (lo hi : ℝ) :
    eval (primitive a p) (a.replace q hi) - eval (primitive a p) (a.replace q lo) =
      ∫ t in lo..hi, eval p (a.replace q t) := by
  induction p with
  | nil => simp [primitive]
  | cons t ts ih =>
    have h₁ : IntervalIntegrable (fun s : ℝ => t.eval (a.replace q s))
        MeasureTheory.volume lo hi := by
      have h := continuous_eval_replace [t] a q
      exact (by simpa using h : Continuous fun s : ℝ => t.eval (a.replace q s)).intervalIntegrable _ _
    have h₂ := (continuous_eval_replace ts a q).intervalIntegrable (μ := MeasureTheory.volume) lo hi
    simp only [primitive, List.map_cons, eval_cons] at ih ⊢
    rw [intervalIntegral.integral_add h₁ h₂, ← eval_term_primitive_sub, ← ih]
    ring

/-- The rational polynomial obtained by integrating in one variable and substituting the bounds. -/
theorem eval_integrate (p lo hi : SparsePoly) (a : Axis) (q : ℝ × ℝ × ℝ) :
    eval (integrate p a lo hi) q = ∫ t in eval lo q..eval hi q, eval p (a.replace q t) := by
  simpa only [integrate, eval_sub, eval_substitute] using
    eval_primitive_sub p a q (eval lo q) (eval hi q)

end SparsePoly
end ZetaSixth

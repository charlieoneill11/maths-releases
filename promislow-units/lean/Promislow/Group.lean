-- SPDX-License-Identifier: Apache-2.0
-- Copyright (c) 2026 Alexander S. Donahue
-- Adapted from lean/PromislowFracton/PromislowGroup.lean at 8b7164514b692747ee62c051b32b0765202f848c.
-- Changes: mathlib Group instance, standard natural powers and integral group ring.
import Mathlib.Algebra.MonoidAlgebra.Basic

namespace Promislow

set_option maxHeartbeats 4000000
/-- The 4 coset representatives of `N = ⟨x, y, z⟩ ≅ ℤ³` in `P`. -/
inductive Coset where
  | e  : Coset   -- 1
  | a  : Coset   -- a
  | b  : Coset   -- b
  | ab : Coset   -- ab
  deriving DecidableEq, Repr, Ord

namespace Coset

def toNat : Coset → Nat
  | e  => 0
  | a  => 1
  | b  => 2
  | ab => 3

/-- Sign action `(s₁, s₂, s₃) ∈ {±1}³` of conjugating `(x, y, z)` by coset `c`:
    `c · x^i y^j z^k = x^{s₁ i} y^{s₂ j} z^{s₃ k} · c`. -/
def signX : Coset → Int
  | e => 1 | a => 1 | b => -1 | ab => -1

def signY : Coset → Int
  | e => 1 | a => -1 | b => 1 | ab => -1

def signZ : Coset → Int
  | e => 1 | a => -1 | b => -1 | ab => 1

/-- Coset multiplication product `c₁ · c₂ = x^{dx} y^{dy} z^{dz} · c₃` in Gardam's basis
    `x = a²`, `y = b²`, `z = (ab)²`. -/
def mulCocycle : Coset → Coset → (Int × Int × Int × Coset)
  | e,  c  => (0, 0, 0, c)
  | c,  e  => (0, 0, 0, c)
  | a,  a  => (1, 0, 0, e)
  | a,  b  => (0, 0, 0, ab)
  | a,  ab => (1, 0, 0, b)
  | b,  a  => (-1, 1, -1, ab)
  | b,  b  => (0, 1, 0, e)
  | b,  ab => (-1, 0, -1, a)
  | ab, a  => (0, -1, 1, b)
  | ab, b  => (0, -1, 0, a)
  | ab, ab => (0, 0, 1, e)

/-- Group multiplication on the quotient `P / N ≅ V₄ = ℤ₂ × ℤ₂`. -/
def mulV4 : Coset → Coset → Coset
  | c₁, c₂ => (mulCocycle c₁ c₂).2.2.2

theorem signX_mul (c₁ c₂ : Coset) : signX (mulV4 c₁ c₂) = signX c₁ * signX c₂ := by
  cases c₁ <;> cases c₂ <;> rfl

theorem signY_mul (c₁ c₂ : Coset) : signY (mulV4 c₁ c₂) = signY c₁ * signY c₂ := by
  cases c₁ <;> cases c₂ <;> rfl

theorem signZ_mul (c₁ c₂ : Coset) : signZ (mulV4 c₁ c₂) = signZ c₁ * signZ c₂ := by
  cases c₁ <;> cases c₂ <;> rfl

end Coset

/-- Normal-form element `x^i y^j z^k · c` of the Promislow / Hantzsche–Wendt group `P`. -/
structure ElemP where
  ix : Int
  iy : Int
  iz : Int
  c  : Coset
  deriving DecidableEq, Repr

namespace ElemP

def one : ElemP := ⟨0, 0, 0, Coset.e⟩
def genA : ElemP := ⟨0, 0, 0, Coset.a⟩
def genB : ElemP := ⟨0, 0, 0, Coset.b⟩
def genAB : ElemP := ⟨0, 0, 0, Coset.ab⟩
def genX : ElemP := ⟨1, 0, 0, Coset.e⟩
def genY : ElemP := ⟨0, 1, 0, Coset.e⟩
def genZ : ElemP := ⟨0, 0, 1, Coset.e⟩

/-- Exact group multiplication in `P`. -/
def mul (g₁ g₂ : ElemP) : ElemP :=
  let (dx, dy, dz, c3) := Coset.mulCocycle g₁.c g₂.c
  ⟨g₁.ix + Coset.signX g₁.c * g₂.ix + dx,
   g₁.iy + Coset.signY g₁.c * g₂.iy + dy,
   g₁.iz + Coset.signZ g₁.c * g₂.iz + dz,
   c3⟩

/-- Exact group inverse in `P`. -/
def inv (g : ElemP) : ElemP :=
  let (dx, dy, dz, _) := Coset.mulCocycle g.c g.c
  ⟨-dx - Coset.signX g.c * g.ix,
   -dy - Coset.signY g.c * g.iy,
   -dz - Coset.signZ g.c * g.iz,
   g.c⟩

/-- Natural-number power in `P`. -/
def pow (g : ElemP) : Nat → ElemP
  | 0 => one
  | k + 1 => mul g (pow g k)

theorem one_mul (g : ElemP) : mul one g = g := by
  cases g with | mk ix iy iz c =>
  cases c <;> simp [mul, one, Coset.mulCocycle, Coset.signX, Coset.signY, Coset.signZ]

theorem mul_one (g : ElemP) : mul g one = g := by
  cases g with | mk ix iy iz c =>
  cases c <;> simp [mul, one, Coset.mulCocycle, Coset.signX, Coset.signY, Coset.signZ]

theorem mul_assoc (g₁ g₂ g₃ : ElemP) : mul (mul g₁ g₂) g₃ = mul g₁ (mul g₂ g₃) := by
  cases g₁ with | mk x1 y1 z1 c1 =>
  cases g₂ with | mk x2 y2 z2 c2 =>
  cases g₃ with | mk x3 y3 z3 c3 =>
  cases c1 <;> cases c2 <;> cases c3 <;>
    simp [mul, Coset.mulCocycle, Coset.signX, Coset.signY, Coset.signZ] <;>
    omega

theorem mul_inv_self (g : ElemP) : mul g (inv g) = one := by
  cases g with | mk ix iy iz c =>
  cases c <;>
    simp [mul, inv, one, Coset.mulCocycle, Coset.signX, Coset.signY, Coset.signZ]

theorem inv_mul_self (g : ElemP) : mul (inv g) g = one := by
  cases g with | mk ix iy iz c =>
  cases c <;>
    simp [mul, inv, one, Coset.mulCocycle, Coset.signX, Coset.signY, Coset.signZ]

theorem inv_inv (g : ElemP) : inv (inv g) = g := by
  cases g with | mk ix iy iz c =>
  cases c <;>
    simp [inv, Coset.mulCocycle, Coset.signX, Coset.signY, Coset.signZ]

theorem inv_mul (g₁ g₂ : ElemP) : inv (mul g₁ g₂) = mul (inv g₂) (inv g₁) := by
  cases g₁ with | mk x1 y1 z1 c1 =>
  cases g₂ with | mk x2 y2 z2 c2 =>
  cases c1 <;> cases c2 <;>
    simp [mul, inv, Coset.mulCocycle, Coset.signX, Coset.signY, Coset.signZ] <;>
    omega

/-- Presentation checks: `a² = x`, `b² = y`, `(ab)² = z`,
    `a⁻¹ b² a = b⁻²`, `b⁻¹ a² b = a⁻²`, and non-Abelianness `ab ≠ ba`. -/
theorem genA_sq : mul genA genA = genX := rfl
theorem genB_sq : mul genB genB = genY := rfl
theorem genAB_sq : mul genAB genAB = genZ := rfl
theorem rel_a_b2 : mul (mul (inv genA) genY) genA = inv genY := rfl
theorem rel_b_a2 : mul (mul (inv genB) genX) genB = inv genX := rfl
theorem non_abelian : mul genA genB ≠ mul genB genA := by decide

/-- Squaring any element in `P` lands in the normal subgroup `N ≅ ℤ³`, with an explicit
    odd-shift obstruction preventing ANY non-identity element from squaring to `1`!
    - `(i, j, k, e)² = (2i, 2j, 2k, e)`
    - `(i, j, k, a)² = (2i + 1, 0, 0, e)`  (NEVER `(0,0,0,e)` because `2i + 1` is odd!)
    - `(i, j, k, b)² = (0, 2j + 1, 0, e)`  (NEVER `(0,0,0,e)` because `2j + 1` is odd!)
    - `(i, j, k, ab)² = (0, 0, 2k + 1, e)` (NEVER `(0,0,0,e)` because `2k + 1` is odd!) -/
theorem sq_in_N (g : ElemP) :
    (mul g g).c = Coset.e ∧
    (g.c = Coset.e → mul g g = ⟨2 * g.ix, 2 * g.iy, 2 * g.iz, Coset.e⟩) ∧
    (g.c = Coset.a → mul g g = ⟨2 * g.ix + 1, 0, 0, Coset.e⟩) ∧
    (g.c = Coset.b → mul g g = ⟨0, 2 * g.iy + 1, 0, Coset.e⟩) ∧
    (g.c = Coset.ab → mul g g = ⟨0, 0, 2 * g.iz + 1, Coset.e⟩) := by
  cases g with | mk ix iy iz c =>
  cases c <;>
    simp [mul, Coset.mulCocycle, Coset.signX, Coset.signY, Coset.signZ] <;>
    omega

/-- Helper: power of a pure translation `(ix, iy, iz, e)` is `(n*ix, n*iy, n*iz, e)`. -/
theorem pow_of_e (ix iy iz : Int) (n : Nat) :
    pow ⟨ix, iy, iz, Coset.e⟩ n = ⟨(n : Int) * ix, (n : Int) * iy, (n : Int) * iz, Coset.e⟩ := by
  induction n with
  | zero => simp [pow, one]
  | succ k ih =>
    simp only [pow, ih, mul, Coset.mulCocycle, Coset.signX, Coset.signY, Coset.signZ, ElemP.mk.injEq, and_true]
    refine ⟨?_, ?_, ?_⟩ <;> grind

/-- Power law `pow g (m + n) = mul (pow g m) (pow g n)`. -/
theorem pow_add (g : ElemP) (m n : Nat) : pow g (m + n) = mul (pow g m) (pow g n) := by
  induction m with
  | zero => simp [pow, one_mul]
  | succ k ih =>
    rw [Nat.succ_add, pow, pow, ih, mul_assoc]

/-- Power law `pow (mul g g) m = pow g (2 * m)`. -/
theorem pow_sq (g : ElemP) (m : Nat) : pow (mul g g) m = pow g (2 * m) := by
  induction m with
  | zero => simp [pow]
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 + 2 * k := by omega
    rw [pow, ih, h2, pow_add]
    simp [pow, mul_one]

/-- **Constructive Torsion-Freeness of the Promislow Group `P`:**
    No non-identity element has finite order. -/
theorem torsion_free (g : ElemP) (n : Nat) (hn : 0 < n) (hpow : pow g n = one) : g = one := by
  -- From g^n = 1 we get g^(2n) = (g^2)^n = 1.
  have h2n : pow (mul g g) n = one := by
    rw [pow_sq, show 2 * n = n + n by omega, pow_add, hpow, one_mul]
  have hsq := sq_in_N g
  cases hc : g.c with
  | e =>
    have he : g = ⟨g.ix, g.iy, g.iz, Coset.e⟩ := by cases g; simp_all
    rw [he, pow_of_e] at hpow
    have hx : (n : Int) * g.ix = 0 := by
      have := congrArg ElemP.ix hpow; exact this
    have hy : (n : Int) * g.iy = 0 := by
      have := congrArg ElemP.iy hpow; exact this
    have hz : (n : Int) * g.iz = 0 := by
      have := congrArg ElemP.iz hpow; exact this
    have hn0 : (n : Int) ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn)
    have hix : g.ix = 0 := (Int.mul_eq_zero.mp hx).resolve_left hn0
    have hiy : g.iy = 0 := (Int.mul_eq_zero.mp hy).resolve_left hn0
    have hiz : g.iz = 0 := (Int.mul_eq_zero.mp hz).resolve_left hn0
    rw [he, hix, hiy, hiz]; rfl
  | a =>
    have ha := hsq.2.2.1 hc
    rw [ha, pow_of_e] at h2n
    have hx : (n : Int) * (2 * g.ix + 1) = 0 := congrArg ElemP.ix h2n
    have hn0 : (n : Int) ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn)
    have hodd : 2 * g.ix + 1 = 0 := (Int.mul_eq_zero.mp hx).resolve_left hn0
    omega
  | b =>
    have hb := hsq.2.2.2.1 hc
    rw [hb, pow_of_e] at h2n
    have hy : (n : Int) * (2 * g.iy + 1) = 0 := congrArg ElemP.iy h2n
    have hn0 : (n : Int) ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn)
    have hodd : 2 * g.iy + 1 = 0 := (Int.mul_eq_zero.mp hy).resolve_left hn0
    omega
  | ab =>
    have hab := hsq.2.2.2.2 hc
    rw [hab, pow_of_e] at h2n
    have hz : (n : Int) * (2 * g.iz + 1) = 0 := congrArg ElemP.iz h2n
    have hn0 : (n : Int) ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.ne_of_gt hn)
    have hodd : 2 * g.iz + 1 = 0 := (Int.mul_eq_zero.mp hz).resolve_left hn0
    omega


end ElemP

instance : Group ElemP where
  one := ElemP.one
  mul := ElemP.mul
  inv := ElemP.inv
  mul_assoc := ElemP.mul_assoc
  one_mul := ElemP.one_mul
  mul_one := ElemP.mul_one
  inv_mul_cancel := ElemP.inv_mul_self

theorem pow_eq (g : ElemP) (n : ℕ) : g ^ n = ElemP.pow g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', ih]; rfl

theorem torsionFree {g : ElemP} {n : ℕ} (hn : 0 < n) (h : g ^ n = 1) : g = 1 :=
  ElemP.torsion_free g n hn ((pow_eq g n).symm.trans h)

abbrev IntegralGroupRing := MonoidAlgebra ℤ ElemP

end Promislow

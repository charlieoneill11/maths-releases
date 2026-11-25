import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

namespace Legendre.Arithmetic

/-- Rational endpoints of an enclosure. -/
structure Bounds where
  lo : ℚ
  hi : ℚ
  deriving Repr, DecidableEq

namespace Bounds

/-- Both endpoints bound the given real value. -/
def Encloses (b : Bounds) (x : ℝ) : Prop := (b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)

def neg (b : Bounds) : Bounds := ⟨-b.hi, -b.lo⟩

def add (a b : Bounds) : Bounds := ⟨a.lo + b.lo, a.hi + b.hi⟩

def smul (q : ℚ) (b : Bounds) : Bounds :=
  if 0 ≤ q then ⟨q * b.lo, q * b.hi⟩ else ⟨q * b.hi, q * b.lo⟩

def abs (b : Bounds) : Bounds :=
  ⟨max 0 (max b.lo (-b.hi)), max |b.lo| |b.hi|⟩

def mul (a b : Bounds) : Bounds :=
  ⟨min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)),
   max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))⟩

theorem neg_sound {b : Bounds} {x : ℝ} (h : b.Encloses x) : b.neg.Encloses (-x) := by
  simpa [Encloses, neg] using And.intro (neg_le_neg h.2) (neg_le_neg h.1)

theorem add_sound {a b : Bounds} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (a.add b).Encloses (x + y) := by
  simpa only [Encloses, add, Rat.cast_add] using
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem smul_sound (q : ℚ) {b : Bounds} {x : ℝ} (h : b.Encloses x) :
    (b.smul q).Encloses ((q : ℝ) * x) := by
  by_cases hq : 0 ≤ q
  · have hq' : 0 ≤ (q : ℝ) := by exact_mod_cast hq
    simpa [Encloses, smul, hq] using
      And.intro (mul_le_mul_of_nonneg_left h.1 hq') (mul_le_mul_of_nonneg_left h.2 hq')
  · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hq)
    simpa [Encloses, smul, hq] using
      And.intro (mul_le_mul_of_nonpos_left h.2 hq') (mul_le_mul_of_nonpos_left h.1 hq')

theorem abs_sound {b : Bounds} {x : ℝ} (h : b.Encloses x) : b.abs.Encloses |x| := by
  simp only [Encloses, abs, Rat.cast_max, Rat.cast_abs, Rat.cast_neg, Rat.cast_zero]
  constructor
  · exact max_le (abs_nonneg _) (max_le (h.1.trans (le_abs_self _))
      ((neg_le_neg h.2).trans (neg_le_abs _)))
  · rw [abs_le]
    exact ⟨(neg_le_neg ((neg_le_abs (b.lo : ℝ)).trans (le_max_left _ _))).trans (by simpa using h.1),
      h.2.trans ((le_abs_self _).trans (le_max_right _ _))⟩

private theorem mul_between (q : ℝ) {lo x hi : ℝ} (hl : lo ≤ x) (hh : x ≤ hi) :
    min (q * lo) (q * hi) ≤ q * x ∧ q * x ≤ max (q * lo) (q * hi) := by
  rcases le_total 0 q with hq | hq
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hl hq),
      (mul_le_mul_of_nonneg_left hh hq).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hh hq),
      (mul_le_mul_of_nonpos_left hl hq).trans (le_max_left _ _)⟩

theorem mul_sound {a b : Bounds} {x y : ℝ} (hx : a.Encloses x) (hy : b.Encloses y) :
    (a.mul b).Encloses (x * y) := by
  simpa only [Encloses, mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul] using
    show min (min ((a.lo : ℝ) * b.lo) ((a.lo : ℝ) * b.hi))
        (min ((a.hi : ℝ) * b.lo) ((a.hi : ℝ) * b.hi)) ≤ x * y ∧
      x * y ≤ max (max ((a.lo : ℝ) * b.lo) ((a.lo : ℝ) * b.hi))
        (max ((a.hi : ℝ) * b.lo) ((a.hi : ℝ) * b.hi)) from by
    have hlo := mul_between (a.lo : ℝ) hy.1 hy.2
    have hhi := mul_between (a.hi : ℝ) hy.1 hy.2
    have hxy := mul_between y hx.1 hx.2
    simp only [mul_comm y] at hxy
    exact ⟨(min_le_min hlo.1 hhi.1).trans hxy.1, hxy.2.trans (max_le_max hlo.2 hhi.2)⟩

end Bounds

/-- Round down to a multiple of `1 / scale`. -/
def roundDown (scale : ℕ) (q : ℚ) : ℚ := ((⌊q * scale⌋ : ℤ) : ℚ) / scale

/-- Round up to a multiple of `1 / scale`. -/
def roundUp (scale : ℕ) (q : ℚ) : ℚ := ((⌈q * scale⌉ : ℤ) : ℚ) / scale

theorem roundDown_le (scale : ℕ) (hs : 0 < scale) (q : ℚ) : roundDown scale q ≤ q :=
  (div_le_iff₀ (by exact_mod_cast hs)).mpr (Int.floor_le _)

theorem le_roundUp (scale : ℕ) (hs : 0 < scale) (q : ℚ) : q ≤ roundUp scale q :=
  (le_div_iff₀ (by exact_mod_cast hs)).mpr (Int.le_ceil _)

def Bounds.round (b : Bounds) (scale : ℕ) : Bounds :=
  ⟨roundDown scale b.lo, roundUp scale b.hi⟩

theorem Bounds.round_sound {b : Bounds} {x : ℝ} (h : b.Encloses x)
    (scale : ℕ) (hs : 0 < scale) : (b.round scale).Encloses x := by
  exact ⟨(Rat.cast_le.mpr (roundDown_le scale hs _)).trans h.1,
    h.2.trans (Rat.cast_le.mpr (le_roundUp scale hs _))⟩

def piBounds : Bounds := ⟨3.14159265358979323846, 3.14159265358979323847⟩

theorem piBounds_sound : piBounds.Encloses Real.pi := by
  constructor
  · simpa [piBounds] using Real.pi_gt_d20.le
  · simpa [piBounds] using Real.pi_lt_d20.le

end Legendre.Arithmetic

import HadwigerNelson.Arithmetic.SquareRoot
import Mathlib.Data.Rat.Floor

/-! Rational intervals for the finite parameter boxes of Proposition 53. -/

namespace HadwigerNelson.Certificate

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving Repr

namespace Interval

def point (x : ℚ) : Interval := ⟨x,x⟩
def add (a b : Interval) : Interval := ⟨a.lo+b.lo, a.hi+b.hi⟩
def sub (a b : Interval) : Interval := ⟨a.lo-b.hi, a.hi-b.lo⟩
def minimum (a b : Interval) : Interval := ⟨min a.lo b.lo,min a.hi b.hi⟩
def maximum (a b : Interval) : Interval := ⟨max a.lo b.lo,max a.hi b.hi⟩
def mul (a b : Interval) : Interval :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩
def floor (a : Interval) : Interval := ⟨(a.lo.floor : ℤ), (a.hi.floor : ℤ)⟩
def sqrtScale : ℕ := 10^10
def rootTicks (x : ℚ) : ℤ := Int.sqrt (max 0 x.floor)
def sqrt (a : Interval) : Interval :=
  ⟨(rootTicks (a.lo*sqrtScale^2) : ℚ)/sqrtScale,
    ((Int.sqrt (max 0 (a.hi*sqrtScale^2).ceil)+1 : ℤ) : ℚ)/sqrtScale⟩

/-- The runtime endpoints enclose the specified real expression. -/
def Contains (a : Interval) (x : ℝ) : Prop := (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ)

theorem point_sound (x : ℚ) : (point x).Contains (x : ℝ) := ⟨le_rfl, le_rfl⟩

variable {a b : Interval} {x y : ℝ}

theorem add_sound (h : a.Contains x) (k : b.Contains y) : (add a b).Contains (x+y) := by
  simpa only [Contains,add,Rat.cast_add] using And.intro (add_le_add h.1 k.1) (add_le_add h.2 k.2)

theorem sub_sound (h : a.Contains x) (k : b.Contains y) : (sub a b).Contains (x-y) := by
  simpa only [Contains,sub,Rat.cast_sub] using And.intro (sub_le_sub h.1 k.2) (sub_le_sub h.2 k.1)

theorem min_sound (h : a.Contains x) (k : b.Contains y) : (minimum a b).Contains (min x y) := by
  simpa only [Contains,minimum,Rat.cast_min] using And.intro (min_le_min h.1 k.1) (min_le_min h.2 k.2)

theorem max_sound (h : a.Contains x) (k : b.Contains y) : (maximum a b).Contains (max x y) := by
  simpa only [Contains,maximum,Rat.cast_max] using And.intro (max_le_max h.1 k.1) (max_le_max h.2 k.2)

private theorem scalar_range {l r t : ℝ} (hl : l ≤ t) (hr : t ≤ r) (c : ℝ) :
    min (l*c) (r*c) ≤ t*c ∧ t*c ≤ max (l*c) (r*c) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hl hc),
      (mul_le_mul_of_nonneg_right hr hc).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hr hc),
      (mul_le_mul_of_nonpos_right hl hc).trans (le_max_left _ _)⟩

theorem mul_sound (h : a.Contains x) (k : b.Contains y) : (mul a b).Contains (x*y) := by
  have lx := scalar_range k.1 k.2 (a.lo : ℝ)
  have rx := scalar_range k.1 k.2 (a.hi : ℝ)
  simp only [mul_comm _ (a.lo : ℝ),mul_comm _ (a.hi : ℝ)] at lx rx
  have hxy := scalar_range h.1 h.2 y
  exact_mod_cast And.intro ((min_le_min lx.1 rx.1).trans hxy.1)
    (hxy.2.trans (max_le_max lx.2 rx.2))

theorem floor_sound (h : a.Contains x) : (floor a).Contains (⌊x⌋ : ℤ) := by
  unfold floor Contains
  push_cast
  constructor
  · exact_mod_cast (Int.floor_le_floor h.1)
  · exact_mod_cast (Int.floor_le_floor h.2)

private theorem ticks_down (q : ℚ) : (rootTicks q : ℝ) ≤ Real.sqrt (q:ℝ) := by
  by_cases hq : 0 ≤ q
  · have hf : 0 ≤ q.floor := Int.floor_nonneg.mpr hq
    unfold rootTicks
    rw [max_eq_right hf]
    apply (Arithmetic.sqrtInt_spec _ hf).1.trans (Real.sqrt_le_sqrt _)
    exact_mod_cast Int.floor_le q
  · have hf : q.floor ≤ 0 := (Int.floor_le_floor (le_of_not_ge hq)).trans_eq (by decide)
    simp only [rootTicks,max_eq_left hf]
    rw [show Int.sqrt 0 = 0 by decide,Int.cast_zero]
    exact Real.sqrt_nonneg _

private theorem ticks_up (q : ℚ) :
    Real.sqrt (q:ℝ) ≤ (Int.sqrt (max 0 q.ceil) : ℝ)+1 := by
  apply (Real.sqrt_le_sqrt _).trans (Arithmetic.sqrtInt_spec _ (le_max_left _ _)).2.le
  exact (show (q:ℝ) ≤ (q.ceil:ℝ) by
    exact_mod_cast @Rat.le_ceil q).trans (by exact_mod_cast le_max_right 0 q.ceil)

private theorem scaled_sqrt (q : ℚ) :
    Real.sqrt ((q * sqrtScale^2 : ℚ):ℝ) = Real.sqrt (q:ℝ)*(sqrtScale:ℝ) := by
  push_cast
  rw [Real.sqrt_mul' _ (sq_nonneg _),Real.sqrt_sq (by positivity)]

theorem sqrt_sound (h : a.Contains x) : (sqrt a).Contains (Real.sqrt x) := by
  have hS : 0 < (sqrtScale:ℝ) := by norm_num [sqrtScale]
  unfold sqrt Contains
  push_cast
  constructor
  · apply (div_le_iff₀ hS).mpr
    have lo := ticks_down (a.lo*sqrtScale^2)
    rw [scaled_sqrt] at lo
    exact lo.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h.1) hS.le)
  · apply (le_div_iff₀ hS).mpr
    have hi := ticks_up (a.hi*sqrtScale^2)
    rw [scaled_sqrt] at hi
    exact (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h.2) hS.le).trans hi

end Interval
end HadwigerNelson.Certificate

import HadwigerNelson.Arithmetic.Phase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp

/-! Angular-length bounds for Proposition 12 and for the signed arc sums in the stars. -/

open Set

namespace HadwigerNelson.Arithmetic

/-- The left endpoint derivative majorizes the arctangent secant on the positive half-line. -/
theorem arctan_sub_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.arctan y - Real.arctan x ≤ (y-x)/(1+x^2) := by
  rcases hxy.eq_or_lt with rfl | hxy
  · simp
  obtain ⟨c, hc, hs⟩ := exists_deriv_eq_slope Real.arctan hxy
    Real.continuous_arctan.continuousOn Real.differentiable_arctan.differentiableOn
  rw [Real.deriv_arctan] at hs
  dsimp only at hs
  have hxden : 0 < 1+x^2 := by positivity
  have hsq : x^2 ≤ c^2 := by nlinarith [sq_nonneg (c-x), mul_nonneg hx (sub_nonneg.mpr hc.1.le)]
  have hd : 1 / (1+c^2) ≤ 1 / (1+x^2) :=
    one_div_le_one_div_of_le hxden (by linarith)
  rw [hs, div_le_div_iff₀ (sub_pos.mpr hxy) hxden] at hd
  exact (le_div_iff₀ hxden).2 (by simpa using hd)

/-- Upper bin length for the half-angle quadrature, before applying integer rounding. -/
theorem arctan_bin_le (N j : Int) (hN : 0 < N) (hj : 0 ≤ j) :
    2 * (Real.arctan (((j:ℝ)+1)/N) - Real.arctan ((j:ℝ)/N)) ≤
      2*(N:ℝ)/((N:ℝ)^2+(j:ℝ)^2) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hjr : (0:ℝ) ≤ j := by exact_mod_cast hj
  have h := arctan_sub_le (x := (j:ℝ)/N) (y := ((j:ℝ)+1)/N)
    (div_nonneg hjr hNr.le) ((div_le_div_iff_of_pos_right hNr).2 (by linarith))
  calc
    _ ≤ 2*(((j+1 : ℝ)/N-(j:ℝ)/N)/(1+((j:ℝ)/N)^2)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by
      have hden : (N:ℝ)^2+(j:ℝ)^2 ≠ 0 := by positivity
      field_simp
      ring

/-- Each short arc is the arctangent of a rational number. -/
theorem arctan_sub_eq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.arctan y - Real.arctan x = Real.arctan ((y-x)/(1+y*x)) := by
  simpa [sub_eq_add_neg] using
    (Real.arctan_add (x := y) (y := -x) (by nlinarith [mul_nonneg hx hy]))

/-- Formula used to accumulate each arc of the moment calculation. -/
theorem arctan_bin_eq (N j : Int) (hN : 0 < N) (hj : 0 ≤ j) :
    Real.arctan (((j:ℝ)+1)/N) - Real.arctan ((j:ℝ)/N) =
      Real.arctan ((N:ℝ)/((N:ℝ)^2+(j:ℝ)*((j:ℝ)+1))) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hjr : (0:ℝ) ≤ j := by exact_mod_cast hj
  rw [arctan_sub_eq (div_nonneg hjr hNr.le) (div_nonneg (by linarith) hNr.le)]
  congr 1
  have hd : (N:ℝ)^2+(j:ℝ)*((j:ℝ)+1) ≠ 0 := by positivity
  field_simp
  ring

/-- Directed rounding of the bin area times its angular width. The incoming area is doubled. -/
theorem weighted_bin_le (N j a : Int) (hN : 0 < N) (hj : 0 ≤ j) (ha : 0 ≤ a) :
    (a:ℝ)*(Real.arctan (((j:ℝ)+1)/N)-Real.arctan ((j:ℝ)/N)) ≤
      (ceilDiv (a*N) (rayDen N j) : ℝ) := by
  have h := arctan_bin_le N j hN hj
  have ha' : (0:ℝ) ≤ a := by exact_mod_cast ha
  have h' := mul_le_mul_of_nonneg_left h ha'
  apply le_trans _ (real_le_ceilDiv _ (rayDen_pos j hN))
  dsimp [rayDen]
  push_cast
  rw [← sq, ← sq]
  simp only [div_eq_mul_inv] at h' ⊢
  linarith only [h']

/-- Taylor bounds used in the rounded arc lengths for the stars. -/
theorem arctan_cubic_enclosure {t : ℝ} (ht : 0 ≤ t) :
    t-t^3/3 ≤ Real.arctan t ∧ Real.arctan t ≤ t := by
  constructor
  · rcases ht.eq_or_lt with rfl | ht
    · simp
    let f (x : ℝ) := Real.arctan x - x + x^3/3
    let f' (x : ℝ) := 1 / (1+x^2) - 1 + x^2
    have hder (x : ℝ) : HasDerivAt f (f' x) x := by
      dsimp [f,f']
      convert ((Real.hasDerivAt_arctan x).sub (hasDerivAt_id x)).add
        (((hasDerivAt_id x).pow 3).div_const 3) using 1
      simp
    obtain ⟨c,hc,hs⟩ := exists_hasDerivAt_eq_slope f f' ht
      (fun x _ => (hder x).continuousAt.continuousWithinAt) (fun x _ => hder x)
    have hden : 0 < 1+c^2 := by positivity
    have hz : 0 ≤ f' c := by
      dsimp [f']
      have he : 1 / (1+c^2) - 1 + c^2 = c^4/(1+c^2) := by field_simp; ring
      rw [he]
      positivity
    rw [hs] at hz
    have hz' := (le_div_iff₀ (sub_pos.mpr ht)).mp hz
    dsimp [f] at hz'
    simp at hz'
    linarith
  · simpa using arctan_sub_le (x := 0) (y := t) le_rfl ht

/-- Cubic lower bound rounded directly as a single signed quotient, also at high precision. -/
theorem rounded_arctan_cubic (m n S : Int) (hm : 0 ≤ m) (hn : 0 < n) (hS : 0 < S) :
    ((2*S*m*(3*n*n-m*m)/(3*n*n*n) : Int) : ℝ) ≤ 2*(S:ℝ)*Real.arctan ((m:ℝ)/n) ∧
    2*(S:ℝ)*Real.arctan ((m:ℝ)/n) ≤ (ceilDiv (2*S*m) n : ℝ) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hS' : (0:ℝ) < S := by exact_mod_cast hS
  obtain ⟨hl,hu⟩ := arctan_cubic_enclosure (t := (m:ℝ)/n) (div_nonneg (by exact_mod_cast hm) hn'.le)
  constructor
  · apply (floorDiv_le_real _ (show 0 < 3*n*n*n by positivity)).trans
    push_cast
    calc
      _ = 2*(S:ℝ)*((m:ℝ)/n-((m:ℝ)/n)^3/3) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
  · apply le_trans _ (real_le_ceilDiv _ hn)
    push_cast
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hu (by positivity)

/-- The complete-wave star's exact bin enclosure at any positive precision. -/
theorem moment_bin_enclosure (N j S : Int) (hN : 0 < N) (hj : 0 ≤ j) (hS : 0 < S) :
    let d := N*N+j*(j+1)
    let angle := 2*(S:ℝ)*(Real.arctan (((j:ℝ)+1)/N)-Real.arctan ((j:ℝ)/N))
    ((2*S*N*(3*d*d-N*N)/(3*d*d*d) : Int) : ℝ) ≤ angle ∧ angle ≤ (ceilDiv (2*S*N) d : ℝ) := by
  dsimp only
  rw [arctan_bin_eq N j hN hj]
  have hd : 0 < N*N+j*(j+1) := by positivity
  have h := rounded_arctan_cubic N (N*N+j*(j+1)) S hN.le hd hS
  simpa only [Int.cast_add,Int.cast_mul,Int.cast_one,Int.cast_pow,← sq] using h

/-- Integer arc weights retain the signs of the upper and lower enclosures. -/
theorem rounded_arctan_weight (m n S : Int) (hm : 0 ≤ m) (hn : 0 < n) (hS : 0 < S)
    (hcubic : 2*(S:ℝ)*((m:ℝ)/n)^3 ≤ 3) :
    (((2*S*m)/n : Int) : ℝ) - 1 ≤ 2*(S:ℝ)*Real.arctan ((m:ℝ)/n) ∧
    2*(S:ℝ)*Real.arctan ((m:ℝ)/n) ≤ (ceilDiv (2*S*m) n : ℝ) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hS' : (0:ℝ) < S := by exact_mod_cast hS
  obtain ⟨hl,hu⟩ := arctan_cubic_enclosure (t := (m:ℝ)/n) (div_nonneg (by exact_mod_cast hm) hn'.le)
  have hfloor := floorDiv_le_real (2*S*m) hn
  have hceil := real_le_ceilDiv (2*S*m) hn
  push_cast at hfloor hceil
  rw [mul_div_assoc] at hfloor hceil
  constructor
  · linarith [mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*(S:ℝ) by positivity)]
  · exact (mul_le_mul_of_nonneg_left hu (by positivity)).trans hceil

end HadwigerNelson.Arithmetic

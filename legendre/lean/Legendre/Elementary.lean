import Legendre.AnalyticData
import Legendre.Claims
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace Legendre

private theorem rpow_gap_lower_bound (x a : ℝ) (hx : 0 ≤ x) (ha : 1 ≤ a) :
    a * x ^ (a - 1) ≤ (x + 1) ^ a - x ^ a := by
  have hd := Real.differentiable_rpow_const ha
  obtain ⟨z, hz, hderiv⟩ := exists_deriv_eq_slope (fun t : ℝ ↦ t ^ a)
    (show x < x + 1 by linarith) hd.continuous.continuousOn hd.differentiableOn
  rw [Real.deriv_rpow_const, show x + 1 - x = 1 by ring, div_one] at hderiv
  rw [← hderiv]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hz.1.le (sub_nonneg.mpr ha))
    (zero_le_one.trans ha)

private theorem rpow_mul_nat_eq {x a : ℝ} (hx : 0 ≤ x) (k m : ℕ)
    (ha : a * (k : ℝ) = (m : ℝ)) : (x ^ a) ^ k = x ^ m := by
  rw [← Real.rpow_mul_natCast hx, ha, Real.rpow_natCast]

private theorem squared_eleven_tenths {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((11 : ℝ) / 10)) ^ (2 : ℕ) = x ^ ((11 : ℝ) / 5) := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

private theorem eleven_tenths_pow_ten {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((11 : ℝ) / 10)) ^ (10 : ℕ) = x ^ (11 : ℕ) :=
  rpow_mul_nat_eq hx 10 11 (by norm_num)

private theorem prime_in_shifted_square_of_endpoint (N : ℕ)
    (h : ∀ m : ℕ, 1 ≤ m → m ≤ N →
      (∃ p : ℕ, p.Prime ∧ m ^ 2 ≤ p ∧ p ≤ m * (m + 1)) ∧
      (∃ p : ℕ, p.Prime ∧ m * (m + 1) ≤ p ∧ p ≤ (m + 1) ^ 2))
    (y : ℝ) (hy : 1 ≤ y) (hyN : y < (N : ℝ))
    (hySq : ∀ p : ℕ, p.Prime → y ^ 2 ≠ (p : ℝ)) : PrimeIn (y ^ 2) ((y + 1) ^ 2) := by
  let m := ⌊y⌋₊
  have hy₀ : 0 ≤ y := zero_le_one.trans hy
  have hm₁ : 1 ≤ m := (Nat.one_le_floor_iff y).2 hy
  have hmN : m < N := (Nat.floor_lt hy₀).2 hyN
  have hmy : (m : ℝ) ≤ y := Nat.floor_le hy₀
  have hym : y < (m : ℝ) + 1 := Nat.lt_floor_add_one y
  by_cases hside : y ^ 2 ≤ (m : ℝ) * ((m : ℝ) + 1)
  · obtain ⟨p, hp, hlo, hhi⟩ := (h m hm₁ hmN.le).2
    have hlo' : (m : ℝ) * ((m : ℝ) + 1) ≤ (p : ℝ) := by exact_mod_cast hlo
    have hhi' : p < (m + 1) ^ 2 := by
      refine lt_of_le_of_ne hhi ?_
      intro hEq
      exact Nat.Prime.not_prime_pow (by decide : 2 ≤ (2 : ℕ)) (hEq ▸ hp)
    have hhi'' : (p : ℝ) < ((m : ℝ) + 1) ^ 2 := by exact_mod_cast hhi'
    refine ⟨p, hp, lt_of_le_of_ne (hside.trans hlo') (hySq p hp), hhi''.trans_le ?_⟩
    exact pow_le_pow_left₀ (by positivity) (add_le_add hmy le_rfl) _
  · obtain ⟨p, hp, hlo, hhi⟩ := (h (m + 1) (by omega) (by omega)).1
    have hne : p ≠ (m + 1) * (m + 1 + 1) := by
      intro hEq
      exact Nat.not_prime_mul (by omega : m + 1 ≠ 1) (by omega : m + 1 + 1 ≠ 1) (hEq ▸ hp)
    have hsucc := Nat.succ_le_of_lt (lt_of_le_of_ne hhi hne)
    have hhi' : (p : ℝ) + 1 ≤ ((m : ℝ) + 1) * ((m : ℝ) + 1 + 1) := by
      exact_mod_cast hsucc
    have hlo' : ((m : ℝ) + 1) ^ 2 ≤ (p : ℝ) := by exact_mod_cast hlo
    have hright : ((m : ℝ) + 1) * ((m : ℝ) + 1 + 1) - 1 < (y + 1) ^ 2 := by
      nlinarith [lt_of_not_ge hside]
    exact ⟨p, hp, (pow_lt_pow_left₀ hym hy₀ (by decide : 2 ≠ (0 : ℕ))).trans_le hlo',
      (by linarith : (p : ℝ) < (y + 1) ^ 2)⟩

/-- Lemma 8 of the paper. -/
theorem prime_in_shifted_square (N : ℕ) (_hN : 1 ≤ N)
    (h : ∀ m : ℕ, 1 ≤ m → m ≤ N →
      (∃ p : ℕ, p.Prime ∧ m ^ 2 ≤ p ∧ p ≤ m * (m + 1)) ∧
      (∃ p : ℕ, p.Prime ∧ m * (m + 1) ≤ p ∧ p ≤ (m + 1) ^ 2))
    (y : ℝ) (hy : 1 ≤ y) (hyN : y < (N : ℝ)) (hySq : ∀ z : ℤ, y ^ 2 ≠ (z : ℝ)) :
    PrimeIn (y ^ 2) ((y + 1) ^ 2) :=
  prime_in_shifted_square_of_endpoint N h y hy hyN (fun p _ ↦ by simpa using hySq (p : ℤ))

private theorem half_square_witnesses (h : CitedFacts) (m : ℕ) (hm : 1 ≤ m)
    (hmN : m ≤ 70_500_000_000_000) :
    (∃ p : ℕ, p.Prime ∧ m ^ 2 ≤ p ∧ p ≤ m * (m + 1)) ∧
    (∃ p : ℕ, p.Prime ∧ m * (m + 1) ≤ p ∧ p ≤ (m + 1) ^ 2) := by
  by_cases h₁ : m = 1
  · subst m
    exact ⟨⟨2, Nat.prime_two, by decide, by decide⟩, ⟨3, Nat.prime_three, by decide, by decide⟩⟩
  · obtain ⟨⟨p, hp, hp₁, hp₂⟩, ⟨q, hq, hq₁, hq₂⟩⟩ := h.sorensonWebster m (by omega) hmN
    exact ⟨⟨p, hp, hp₁.le, hp₂.le⟩, ⟨q, hq, hq₁.le, hq₂.le⟩⟩

/-- The exact cutoff used in Proposition 3. -/
theorem low_range_cutoff :
    (3_883_853_444_450 : ℕ) ^ 11 < 70_500_000_000_000 ^ 10 ∧
      70_500_000_000_000 ^ 10 < (3_883_853_444_450 + 1) ^ 11 := by decide

/-- Proposition 3 of the paper. -/
theorem low_range (h : CitedFacts) (n : ℕ) (hn : 1 ≤ n) (hcut : n ≤ 3_883_853_444_450) :
    PrimeIn ((n : ℝ) ^ ((11 : ℝ) / 5)) (((n : ℝ) + 1) ^ ((11 : ℝ) / 5)) := by
  let y := (n : ℝ) ^ ((11 : ℝ) / 10)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy : 1 ≤ y := Real.one_le_rpow hn' (by norm_num)
  have hcutNat : n ^ 11 < (70_500_000_000_000 : ℕ) ^ 10 :=
    (Nat.pow_le_pow_left hcut 11).trans_lt low_range_cutoff.1
  have hyN : y < (70_500_000_000_000 : ℝ) := by
    apply (pow_lt_pow_iff_left₀ (n := 10) (zero_le_one.trans hy) (by norm_num) (by decide)).1
    rw [eleven_tenths_pow_ten (Nat.cast_nonneg n)]
    exact_mod_cast hcutNat
  have hysq : y ^ 2 = (n : ℝ) ^ ((11 : ℝ) / 5) := squared_eleven_tenths (Nat.cast_nonneg n)
  have hendpoint (p : ℕ) (hp : p.Prime) : y ^ 2 ≠ (p : ℝ) :=
    hysq ▸ powerEndpoint_ne_prime n p hp
  obtain ⟨p, hp, hlo, hhi⟩ :=
    prime_in_shifted_square_of_endpoint 70_500_000_000_000 (half_square_witnesses h) y hy
      (by exact_mod_cast hyN) hendpoint
  have hgap := rpow_gap_lower_bound (n : ℝ) (11 / 10) (Nat.cast_nonneg n) (by norm_num)
  have hpow : 1 ≤ (n : ℝ) ^ ((11 : ℝ) / 10 - 1) := Real.one_le_rpow hn' (by norm_num)
  have hyhi : y + 1 ≤ ((n : ℝ) + 1) ^ ((11 : ℝ) / 10) := by
    dsimp [y]
    nlinarith [mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 11 / 10)]
  have hbound := pow_le_pow_left₀ (n := 2) (by positivity : 0 ≤ y + 1) hyhi
  rw [squared_eleven_tenths (by positivity)] at hbound
  exact ⟨p, hp, hysq ▸ hlo, hhi.trans_le hbound⟩

/-- Lemma 9 of the paper. -/
theorem square_interval_nested (n : ℕ) (hn : 400 ≤ n) (hcut : n ^ 11 ≤ 10 ^ 140) :
    let m := ⌈(n : ℝ) ^ ((11 : ℝ) / 10)⌉₊
    1 ≤ m ∧ m ≤ 10 ^ 14 ∧
      (n : ℝ) ^ ((11 : ℝ) / 5) ≤ (m : ℝ) ^ 2 ∧
      ((m : ℝ) + 1) ^ 2 < ((n : ℝ) + 1) ^ ((11 : ℝ) / 5) := by
  let y := (n : ℝ) ^ ((11 : ℝ) / 10)
  let m := ⌈y⌉₊
  change 1 ≤ m ∧ m ≤ 10 ^ 14 ∧ _
  have hn' : (400 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hy : 0 < y := Real.rpow_pos_of_pos (by linarith) _
  have hmy : y ≤ (m : ℝ) := Nat.le_ceil y
  have hm₁ : (m : ℝ) < y + 1 := Nat.ceil_lt_add_one hy.le
  have hycap : y ≤ (10 : ℝ) ^ (14 : ℕ) := by
    apply (pow_le_pow_iff_left₀ (n := 10) hy.le (by positivity) (by decide)).1
    rw [eleven_tenths_pow_ten hn₀, ← pow_mul]
    exact_mod_cast hcut
  have hsmall : (20 / 11 : ℝ) < (400 : ℝ) ^ ((1 : ℝ) / 10) := by
    apply (pow_lt_pow_iff_left₀ (n := 10) (by positivity) (by positivity) (by decide)).1
    rw [rpow_mul_nat_eq (by norm_num : (0 : ℝ) ≤ 400) 10 1 (by norm_num), pow_one]
    norm_num
  have hroot := hsmall.trans_le
    (Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 400) hn' (by norm_num : (0 : ℝ) ≤ 1 / 10))
  have hgap := rpow_gap_lower_bound (n : ℝ) (11 / 10) hn₀ (by norm_num)
  rw [show (11 / 10 : ℝ) - 1 = 1 / 10 by norm_num] at hgap
  have hyhi : (m : ℝ) + 1 < ((n : ℝ) + 1) ^ ((11 : ℝ) / 10) := by
    dsimp [y] at hm₁
    linarith
  refine ⟨Nat.one_le_ceil_iff.2 hy, Nat.ceil_le.2 (by exact_mod_cast hycap), ?_, ?_⟩
  · rw [← squared_eleven_tenths hn₀]
    exact pow_le_pow_left₀ hy.le hmy _
  · rw [← squared_eleven_tenths (by positivity)]
    exact pow_lt_pow_left₀ hyhi (by positivity) (by decide)

/-- Lemma 10 of the paper. -/
theorem prime_in_cms_interval (hRH : RiemannHypothesis) (h : CitedFacts)
    (X Y : ℝ) (hY : 5 ≤ Y)
    (hwide : Y - X - 1 / 2 > (22 / 25) * Real.sqrt Y * Real.log Y) : PrimeIn X Y := by
  have hY₀ : 0 < Y := by linarith
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  by_cases hX : 4 ≤ X
  · let u := X + 1 / 4
    have hu₄ : 4 ≤ u := by dsimp [u]; linarith
    have hu₀ : 0 < u := by linarith
    have huY : u < Y := by
      have : 0 ≤ (22 / 25 : ℝ) * Real.sqrt Y * Real.log Y := by positivity
      dsimp [u]
      linarith
    have hmonotone : Real.sqrt u * Real.log u ≤ Real.sqrt Y * Real.log Y :=
      mul_le_mul (Real.sqrt_le_sqrt huY.le) (Real.log_le_log hu₀ huY.le)
        (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg Y)
    obtain ⟨p, hp, hplo, hphi⟩ := h.cms hRH u hu₄
    have hupper : (p : ℝ) ≤ u + (22 / 25) * (Real.sqrt Y * Real.log Y) := by
      calc
        (p : ℝ) ≤ u + (22 / 25) * Real.sqrt u * Real.log u := hphi
        _ = u + (22 / 25) * (Real.sqrt u * Real.log u) := by ring
        _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hmonotone (by norm_num))
    exact ⟨p, hp, by dsimp [u] at hplo; linarith, by dsimp [u] at hupper; linarith⟩
  · rcases hY.lt_or_eq with hY' | rfl
    · exact ⟨5, by decide, by norm_num; linarith, by exact_mod_cast hY'⟩
    · have hsqrt : (2 : ℝ) ≤ Real.sqrt 5 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
      have hlog : (1 : ℝ) ≤ Real.log 5 := (Real.le_log_iff_exp_le (by norm_num)).2
        (Real.exp_one_lt_three.le.trans (by norm_num))
      have hterm := mul_le_mul hsqrt hlog (by norm_num) (Real.sqrt_nonneg 5)
      exact ⟨3, Nat.prime_three, by norm_num; nlinarith, by norm_num⟩

/-- Rational enclosures at the start of the CMS range. -/
theorem cms_cutoff_bounds :
    (30.0479 : ℝ) < (6 * 10 ^ 14 : ℝ) ^ ((1 : ℝ) / 10) ∧
      Real.log (6 * 10 ^ 14) < 34.028 := by
  constructor
  · apply (pow_lt_pow_iff_left₀ (n := 10) (by positivity) (by positivity) (by decide)).1
    rw [rpow_mul_nat_eq (by positivity : (0 : ℝ) ≤ 6 * 10 ^ 14) 10 1 (by norm_num), pow_one]
    norm_num
  · rw [Real.log_lt_iff_lt_exp (by positivity), show (34.028 : ℝ) = 34 + 0.028 by norm_num,
      Real.exp_add]
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
      Real.exp_one_gt_d9.le 34
    rw [Real.exp_one_pow] at hpow
    calc
      (6 * 10 ^ 14 : ℝ) < (2.7182818283 : ℝ) ^ (34 : ℕ) * (1 + 0.028 + 0.028 ^ (2 : ℕ) / 2) := by
        norm_num
      _ ≤ Real.exp 34 * Real.exp 0.028 := mul_le_mul hpow
        (Real.quadratic_le_exp_of_nonneg (by norm_num)) (by norm_num) (by positivity)

/-- The scalar comparison in Corollary 11, with a positive margin of `0.1`. -/
theorem cms_comparison_margin (x : ℝ) (hx : 6 * 10 ^ 14 ≤ x) :
    0.1 < x ^ ((1 : ℝ) / 10) - (22 / 25) * (1 + 2 / 10 ^ 15) *
      (Real.log x + 2 / 10 ^ 15) - 2 / 10 ^ 17 := by
  let x₀ : ℝ := 6 * 10 ^ 14
  let r₀ : ℝ := x₀ ^ ((1 : ℝ) / 10)
  let c : ℝ := (22 / 25) * (1 + 2 / 10 ^ 15)
  have hx₀ : 0 < x₀ := by norm_num [x₀]
  have hx' : x₀ ≤ x := hx
  have hxpos : 0 < x := hx₀.trans_le hx'
  have hr₀ : 30.0479 < r₀ := cms_cutoff_bounds.1
  have hlog : Real.log x₀ ≤ Real.log x := Real.log_le_log hx₀ hx'
  have hroot : x ^ ((1 : ℝ) / 10) = r₀ * Real.exp ((Real.log x - Real.log x₀) / 10) := by
    rw [show r₀ = x₀ ^ ((1 : ℝ) / 10) by rfl, Real.rpow_def_of_pos hxpos,
      Real.rpow_def_of_pos hx₀, ← Real.exp_add]
    congr 1
    ring
  have hbase : 0.1 < r₀ - c * (Real.log x₀ + 2 / 10 ^ 15) - 2 / 10 ^ 17 := by
    have hlog₀ : Real.log x₀ < 34.028 := cms_cutoff_bounds.2
    dsimp [c]
    linarith only [hr₀, hlog₀]
  have hc : c ≤ r₀ / 10 := by dsimp [c]; linarith only [hr₀]
  have hgrowth := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hlog)
  have hge : r₀ * (1 + (Real.log x - Real.log x₀) / 10) ≤ x ^ ((1 : ℝ) / 10) := by
    rw [hroot]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hr₀])
    simpa only [add_comm] using Real.add_one_le_exp ((Real.log x - Real.log x₀) / 10)
  change 0.1 < x ^ ((1 : ℝ) / 10) - c * (Real.log x + 2 / 10 ^ 15) - 2 / 10 ^ 17
  linarith only [hbase, hgrowth, hge]

/-- Corollary 11 of the paper. -/
theorem far_range (hRH : RiemannHypothesis) (h : CitedFacts) (x : ℝ) (hx : 6 * 10 ^ 14 ≤ x) :
    PrimeIn (x ^ ((11 : ℝ) / 5)) ((x + 1) ^ ((11 : ℝ) / 5)) := by
  let X := x ^ ((11 : ℝ) / 5)
  let Y := (x + 1) ^ ((11 : ℝ) / 5)
  let ε : ℝ := 2 / 10 ^ 15
  let t : ℝ := 1 + 1 / x
  let d : ℝ := (11 / 5) * x ^ ((11 : ℝ) / 10)
  have hx₁ : 1 ≤ x := by linarith only [hx]
  have hx₀ : 0 < x := by linarith only [hx₁]
  have ht₁ : 1 ≤ t := by
    dsimp [t]
    exact le_add_of_nonneg_right (by positivity)
  have ht₀ : 0 < t := by linarith only [ht₁]
  have hd : 0 < d := by dsimp [d]; positivity
  have hε : 0 < ε := by norm_num [ε]
  have hxt : x * t = x + 1 := by dsimp [t]; field_simp
  have hrecrip : 1 / x ≤ (1 / (6 * 10 ^ 14) : ℝ) := one_div_le_one_div_of_le (by norm_num) hx
  have hlogt : Real.log t ≤ 1 / x := by
    have hh := Real.log_le_sub_one_of_pos ht₀
    dsimp [t] at hh
    linarith only [hh]
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx₁
  have hlogx' : Real.log (x + 1) ≤ Real.log x + ε := by
    rw [← hxt, Real.log_mul hx₀.ne' ht₀.ne']
    dsimp [ε]
    linarith only [hlogt, hrecrip]
  have ht_pow : t ^ ((11 : ℝ) / 10) ≤ 1 + ε := by
    let a : ℝ := 1.9 / 10 ^ 15
    have ha : 0 ≤ a := by norm_num [a]
    have ha' : a < 1 := by norm_num [a]
    have harg : Real.log t * (11 / 10) ≤ a := by
      dsimp [a]
      linarith only [hlogt, hrecrip]
    rw [Real.rpow_def_of_pos ht₀]
    exact (Real.exp_le_exp.2 harg).trans
      ((Real.exp_bound_div_one_sub_of_interval ha ha').trans (by norm_num [a, ε]))
  have hsqrtY : Real.sqrt Y = (x + 1) ^ ((11 : ℝ) / 10) := by
    dsimp [Y]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ x + 1)]
    norm_num
  have hsqrtY' : Real.sqrt Y ≤ (1 + ε) * x ^ ((11 : ℝ) / 10) := by
    rw [hsqrtY, ← hxt, Real.mul_rpow hx₀.le ht₀.le, mul_comm (1 + ε)]
    exact mul_le_mul_of_nonneg_left ht_pow (by positivity)
  have hlogY : Real.log Y = (11 / 5) * Real.log (x + 1) := Real.log_rpow (by positivity) _
  have hlogY' : Real.log Y ≤ (11 / 5) * (Real.log x + ε) :=
    hlogY.trans_le (mul_le_mul_of_nonneg_left hlogx' (by norm_num))
  have hpows : x ^ ((11 : ℝ) / 10) * x ^ ((1 : ℝ) / 10) = x ^ ((11 : ℝ) / 5 - 1) := by
    rw [← Real.rpow_add hx₀]
    norm_num
  have hgap : d * x ^ ((1 : ℝ) / 10) ≤ Y - X := by
    dsimp [d, X, Y]
    rw [mul_assoc, hpows]
    exact rpow_gap_lower_bound x (11 / 5) hx₀.le (by norm_num)
  have hroot : (30 : ℝ) ≤ x ^ ((1 : ℝ) / 10) :=
    (by norm_num : (30 : ℝ) ≤ 30.0479).trans <| cms_cutoff_bounds.1.le.trans <|
      Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have hhalf : (1 / 2 : ℝ) ≤ d * (2 / 10 ^ 17) := by
    have hprod := mul_le_mul hx hroot (by norm_num : (0 : ℝ) ≤ 30) hx₀.le
    have hpow : x ^ ((11 : ℝ) / 10) = x * x ^ ((1 : ℝ) / 10) := by
      rw [show (11 / 10 : ℝ) = 1 + 1 / 10 by norm_num, Real.rpow_add hx₀, Real.rpow_one]
    dsimp [d]
    rw [hpow]
    linarith only [hprod]
  have hY : (5 : ℝ) ≤ Y := by
    calc
      (5 : ℝ) ≤ x + 1 := by linarith only [hx]
      _ = (x + 1) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Y := Real.rpow_le_rpow_of_exponent_le (by linarith only [hx₁]) (by norm_num)
  have hlogY₀ : 0 ≤ Real.log Y := Real.log_nonneg (by linarith only [hY])
  refine prime_in_cms_interval hRH h X Y hY ?_
  calc
    (22 / 25 : ℝ) * Real.sqrt Y * Real.log Y ≤
        d * ((22 / 25) * (1 + ε) * (Real.log x + ε)) := by
          dsimp [d]
          calc
            (22 / 25 : ℝ) * Real.sqrt Y * Real.log Y
                = (22 / 25 : ℝ) * (Real.sqrt Y * Real.log Y) := by ring
            _ ≤ (22 / 25 : ℝ) * (((1 + ε) * x ^ ((11 : ℝ) / 10)) *
                ((11 / 5) * (Real.log x + ε))) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul hsqrtY' hlogY' hlogY₀ (by positivity)) (by norm_num)
            _ = _ := by ring
    _ < d * (x ^ ((1 : ℝ) / 10) - 2 / 10 ^ 17) := by
      apply mul_lt_mul_of_pos_left _ hd
      have hm := cms_comparison_margin x hx
      change 0.1 < x ^ ((1 : ℝ) / 10) - (22 / 25) * (1 + ε) * (Real.log x + ε) - 2 / 10 ^ 17 at hm
      linarith only [hm]
    _ = d * x ^ ((1 : ℝ) / 10) - d * (2 / 10 ^ 17) := by ring
    _ ≤ Y - X - 1 / 2 := sub_le_sub hgap hhalf

/-- Theorem 2 of the paper. -/
theorem squares_of (h : CitedFacts) (c : ComputationClaims) : SquaresStatement := by
  intro m hm₁ hm₂
  by_cases h₁ : m = 1
  · subst m
    exact ⟨2, Nat.prime_two, by decide, by decide⟩
  by_cases hcut : m ≤ 70_500_000_000_000
  · obtain ⟨⟨p, hp, hlo, hhi⟩, -⟩ := h.sorensonWebster m (by omega) hcut
    have hbound : m * (m + 1) ≤ (m + 1) ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_right _ (Nat.le_succ m)
    exact ⟨p, hp, hlo, hhi.trans_le hbound⟩
  · exact c.squares m (lt_of_not_ge hcut) hm₂

/-- The final power base covered by square nesting. -/
theorem finite_range_cutoff :
    (5_336_699_231_206 : ℕ) ^ 11 ≤ 10 ^ 140 ∧
      10 ^ 140 < (5_336_699_231_206 + 1) ^ 11 := by decide

/-- Proposition 5 of the paper. -/
theorem finite_range (h : CitedFacts) (c : ComputationClaims) (n : ℕ)
    (hn : 3_883_853_444_450 < n) (hcut : n < 35 * 10 ^ 12) :
    ∃ p : ℕ, p.Prime ∧ n ^ 11 < p ^ 5 ∧ p ^ 5 < (n + 1) ^ 11 := by
  by_cases hn₂ : n ≤ 5_336_699_231_206
  · have hpow : n ^ 11 ≤ 10 ^ 140 := (Nat.pow_le_pow_left hn₂ 11).trans finite_range_cutoff.1
    let m := ⌈(n : ℝ) ^ ((11 : ℝ) / 10)⌉₊
    have hm : 1 ≤ m ∧ m ≤ 10 ^ 14 ∧
        (n : ℝ) ^ ((11 : ℝ) / 5) ≤ (m : ℝ) ^ 2 ∧
        ((m : ℝ) + 1) ^ 2 < ((n : ℝ) + 1) ^ ((11 : ℝ) / 5) :=
      square_interval_nested n (by omega) hpow
    obtain ⟨p, hp, hlo, hhi⟩ := squares_of h c m hm.1 hm.2.1
    have hlo' : (m : ℝ) ^ 2 < (p : ℝ) := by exact_mod_cast hlo
    have hhi' : (p : ℝ) < ((m : ℝ) + 1) ^ 2 := by exact_mod_cast hhi
    exact ⟨p, hp, (powerInterval_iff n p).mp ⟨hm.2.2.1.trans_lt hlo', hhi'.trans hm.2.2.2⟩⟩
  · exact c.powers n (lt_of_not_ge hn₂) hcut

/-- The low, finite and large ranges assemble to Theorem 1. -/
theorem main_of_outer (outer : OuterStatement) (h : CitedFacts) (c : ComputationClaims) :
    MainStatement := by
  intro n hn
  by_cases hlow : n ≤ 3_883_853_444_450
  · exact low_range h n hn hlow
  by_cases hfinite : n < 35 * 10 ^ 12
  · obtain ⟨p, hp, hmem⟩ := finite_range h c n (lt_of_not_ge hlow) hfinite
    exact ⟨p, hp, (powerInterval_iff n p).mpr hmem⟩
  · exact outer n (by exact_mod_cast le_of_not_gt hfinite)

end Legendre

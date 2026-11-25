import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace Chowla

open Filter
open scoped ArithmeticFunction.Moebius BigOperators Topology

noncomputable def residueClassFour (r : ℕ) (X : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊X⌋₊).filter (fun n => n % 4 = r)

noncomputable def squarefreeResidueClassFour (r : ℕ) (X : ℝ) : Finset ℕ :=
  (residueClassFour r X).filter Squarefree

private theorem residueClassFour_card (r : ℕ) (hr₀ : 0 < r) (hr₄ : r < 4) (X : ℝ) :
    (residueClassFour r X).card = (⌊X⌋₊ + 4 - r) / 4 := by
  rw [← Finset.card_range ((⌊X⌋₊ + 4 - r) / 4)]
  refine Finset.card_bij' (s := residueClassFour r X)
    (t := Finset.range ((⌊X⌋₊ + 4 - r) / 4))
    (fun n _ => n / 4) (fun k _ => 4 * k + r) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [residueClassFour, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    change n / 4 < (⌊X⌋₊ + 4 - r) / 4
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [residueClassFour, Finset.mem_filter, Finset.mem_Icc]
    omega
  · intro n hn
    simp only [residueClassFour, Finset.mem_filter, Finset.mem_Icc] at hn
    change 4 * (n / 4) + r = n
    omega
  · intro k _
    change (4 * k + r) / 4 = k
    omega

theorem residueClassFour_card_le (r : ℕ) {X : ℝ} (hX : 0 ≤ X) :
    ((residueClassFour r X).card : ℝ) ≤ X := by
  have h := Finset.card_le_card (Finset.filter_subset (fun n : ℕ => n % 4 = r) (Finset.Icc 1 ⌊X⌋₊))
  have h' : (residueClassFour r X).card ≤ ⌊X⌋₊ := by simpa [residueClassFour] using h
  exact (Nat.cast_le.mpr h').trans (Nat.floor_le hX)

theorem tendsto_residueClassFour_card (r : ℕ) (hr₀ : 0 < r) (hr₄ : r < 4) :
    Tendsto (fun X : ℝ => ((residueClassFour r X).card : ℝ) / X) atTop (𝓝 (1 / 4)) := by
  have hlim : Tendsto (fun X : ℝ => 2 / X) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul (2 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using tendsto_const_nhds.sub hlim)
    (by simpa only [add_zero] using tendsto_const_nhds.add hlim) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have h := residueClassFour_card r hr₀ hr₄ X
    have hn : ⌊X⌋₊ ≤ 4 * (residueClassFour r X).card + 4 := by omega
    have hc : (⌊X⌋₊ : ℝ) ≤ 4 * ((residueClassFour r X).card : ℝ) + 4 := by exact_mod_cast hn
    apply (le_div_iff₀ hX).mpr
    rw [sub_mul, div_mul_cancel₀ _ hX.ne']
    linarith [Nat.lt_floor_add_one X]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have h := residueClassFour_card r hr₀ hr₄ X
    have hn : 4 * (residueClassFour r X).card ≤ ⌊X⌋₊ + 4 := by omega
    have hc : 4 * ((residueClassFour r X).card : ℝ) ≤ (⌊X⌋₊ : ℝ) + 4 := by exact_mod_cast hn
    apply (div_le_iff₀ hX).mpr
    rw [add_mul, div_mul_cancel₀ _ hX.ne']
    linarith [Nat.floor_le hX.le]

private theorem moebius_square_divisor_sum (n N : ℕ) (hn : 0 < n) (hN : n ≤ N) :
    (∑ a ∈ Finset.Icc 1 N with a^2 ∣ n, μ a) = if Squarefree n then 1 else 0 := by
  classical
  let b := Nat.floorRoot 2 n
  have hb : b ≠ 0 := Nat.floorRoot_ne_zero.mpr ⟨by decide, hn.ne'⟩
  have hsub : (Finset.Icc 1 N).filter (fun a => a^2 ∣ n) = b.divisors := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · exact fun h => ⟨Nat.pow_dvd_iff_dvd_floorRoot.mp h.2, hb⟩
    · rintro ⟨ha, _⟩
      have hapos : 0 < a := Nat.pos_of_dvd_of_pos ha (Nat.pos_of_ne_zero hb)
      have haq : a^2 ∣ n := Nat.pow_dvd_iff_dvd_floorRoot.mpr ha
      have hle : a ≤ a^2 := by nlinarith
      exact ⟨⟨hapos, (hle.trans (Nat.le_of_dvd hn haq)).trans hN⟩, haq⟩
  rw [hsub, ← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
    ArithmeticFunction.one_apply]
  have hiff : b = 1 ↔ Squarefree n := by
    constructor
    · intro hb1 a ha
      rw [← pow_two] at ha
      exact Nat.isUnit_iff.mpr (Nat.dvd_one.mp (hb1 ▸ Nat.pow_dvd_iff_dvd_floorRoot.mp ha))
    · intro hsf
      exact Nat.isUnit_iff.mp (hsf b (by
        simpa only [pow_two] using (Nat.floorRoot_pow_dvd (n := 2) (a := n))))
  simp only [hiff]

private noncomputable def residueSquareMultiples (r a : ℕ) (X : ℝ) : Finset ℕ :=
  (residueClassFour r X).filter (fun n => a^2 ∣ n)

private theorem square_mod_four_of_odd {a : ℕ} (ha : Odd a) : a^2 % 4 = 1 := by
  rw [pow_two, Nat.mul_mod]
  obtain h | h := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp ha) <;> rw [h]

private theorem residueSquareMultiples_card (r a : ℕ) {X : ℝ}
    (hX : 0 ≤ X) (ha : Odd a) :
    (residueSquareMultiples r a X).card = (residueClassFour r (X / (a : ℝ)^2)).card := by
  have hq : 0 < a^2 := pow_pos ha.pos _
  have hqR : 0 < (a : ℝ)^2 := by exact_mod_cast hq
  have hY : 0 ≤ X / (a : ℝ)^2 := div_nonneg hX hqR.le
  have hmod (m : ℕ) : (m * a^2) % 4 = m % 4 := by
    rw [Nat.mul_mod, square_mod_four_of_odd ha, mul_one, Nat.mod_mod]
  refine Finset.card_bij' (s := residueSquareMultiples r a X)
    (t := residueClassFour r (X / (a : ℝ)^2))
    (fun n _ => n / a^2) (fun m _ => m * a^2) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨⟨⟨hn₁, hn₂⟩, hR⟩, hdiv⟩ :
        ((1 ≤ n ∧ n ≤ ⌊X⌋₊) ∧ n % 4 = r) ∧ a^2 ∣ n := by
      simpa only [residueSquareMultiples, residueClassFour, Finset.mem_filter, Finset.mem_Icc] using hn
    have hmul := Nat.div_mul_cancel hdiv
    have hn₁' : 1 ≤ n / a^2 := by
      apply Nat.pos_of_ne_zero
      intro h
      simp [h] at hmul
      omega
    have hnr : ((n : ℕ) : ℝ) ≤ X := (Nat.le_floor_iff hX).mp hn₂
    have hbound : (n / a^2 : ℕ) ≤ ⌊X / (a : ℝ)^2⌋₊ := by
      apply (Nat.le_floor_iff hY).mpr
      apply (le_div_iff₀ hqR).mpr
      have heq : ((n / a^2 : ℕ) : ℝ) * (a : ℝ)^2 = (n : ℝ) := by exact_mod_cast hmul
      exact heq ▸ hnr
    have hR' : (n / a^2) % 4 = r := by rw [← hmod, hmul, hR]
    simpa only [residueClassFour, Finset.mem_filter, Finset.mem_Icc] using And.intro (And.intro hn₁' hbound) hR'
  · intro m hm
    obtain ⟨hmin, hR⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm₁, hm₂⟩ := Finset.mem_Icc.mp hmin
    have hbound : m * a^2 ≤ ⌊X⌋₊ := by
      apply (Nat.le_floor_iff hX).mpr
      push_cast
      exact (le_div_iff₀ hqR).mp ((Nat.le_floor_iff hY).mp hm₂)
    have hmP : 1 ≤ m * a^2 := Nat.mul_pos hm₁ hq
    have hmD : a^2 ∣ m * a^2 := dvd_mul_left _ _
    simpa only [residueSquareMultiples, residueClassFour, Finset.mem_filter, Finset.mem_Icc]
      using And.intro (And.intro (And.intro hmP hbound) ((hmod m).trans hR)) hmD
  · exact fun n hn => Nat.div_mul_cancel (Finset.mem_filter.mp hn).2
  · exact fun m _ => Nat.mul_div_cancel _ hq

private theorem residueSquareMultiples_card_zero {r a : ℕ} (hr : Odd r) (ha : ¬ Odd a)
    (X : ℝ) : (residueSquareMultiples r a X).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  simp only [residueSquareMultiples, residueClassFour, Finset.mem_filter, Finset.mem_Icc] at hn
  have hmod : r % 2 = 1 := Nat.odd_iff.mp hr
  have hed : 2 ∣ a := by
    rw [Nat.dvd_iff_mod_eq_zero]
    rw [Nat.odd_iff] at ha
    omega
  have hEvenN : 2 ∣ n := dvd_trans (by simpa only [pow_two] using dvd_trans hed (dvd_mul_right a a)) hn.2
  omega

private noncomputable def squarefreeSieveTerm (r : ℕ) (X : ℝ) (a : ℕ) : ℝ :=
  (μ a : ℝ) * (residueSquareMultiples r a X).card / X

private theorem squarefreeSieveTerm_support (r : ℕ) (X : ℝ) {a : ℕ}
    (ha : a ∉ Finset.Icc 1 ⌊X⌋₊) : squarefreeSieveTerm r X a = 0 := by
  by_cases h₀ : a = 0
  · simp [squarefreeSieveTerm, h₀]
  have hcard : (residueSquareMultiples r a X).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    simp only [residueSquareMultiples, residueClassFour, Finset.mem_filter, Finset.mem_Icc] at hn
    have hle : a ≤ a^2 := by have : 0 < a := Nat.pos_of_ne_zero h₀; nlinarith
    have haq := hle.trans (Nat.le_of_dvd (Nat.zero_lt_of_lt (Nat.zero_lt_one.trans_le hn.1.1.1)) hn.2)
    exact ha (Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero h₀, haq.trans hn.1.1.2⟩)
  simp [squarefreeSieveTerm, hcard]

private theorem squarefreeSieveTerm_tsum (r : ℕ) (X : ℝ) :
    ∑' a, squarefreeSieveTerm r X a = ((squarefreeResidueClassFour r X).card : ℝ) / X := by
  classical
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊X⌋₊) (fun a ha => squarefreeSieveTerm_support r X ha)]
  simp only [squarefreeSieveTerm, div_eq_mul_inv, ← Finset.sum_mul]
  congr 1
  calc
    (∑ a ∈ Finset.Icc 1 ⌊X⌋₊, (μ a : ℝ) * (residueSquareMultiples r a X).card) =
        ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, ∑ n ∈ residueClassFour r X, if a^2 ∣ n then (μ a : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_filter]
      simp [residueSquareMultiples, mul_comm]
    _ = ∑ n ∈ residueClassFour r X, ∑ a ∈ Finset.Icc 1 ⌊X⌋₊, if a^2 ∣ n then (μ a : ℝ) else 0 :=
      Finset.sum_comm
    _ = ∑ n ∈ residueClassFour r X, if Squarefree n then (1 : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn₂ := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
      rw [← Finset.sum_filter]
      exact_mod_cast moebius_square_divisor_sum n ⌊X⌋₊ hn₂.1 hn₂.2
    _ = ((squarefreeResidueClassFour r X).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [squarefreeResidueClassFour]

/-- The odd-indexed coefficients of the Möbius Dirichlet series at two. -/
noncomputable def oddMoebiusTerm (a : ℕ) : ℝ :=
  if Odd a then (μ a : ℝ) / (a : ℝ)^2 else 0

private theorem squarefreeSieveTerm_bound (r a : ℕ) (hr : Odd r) {X : ℝ} (hX : 0 < X) :
    ‖squarefreeSieveTerm r X a‖ ≤ 1 / (a : ℝ)^2 := by
  by_cases ha : Odd a
  · rw [squarefreeSieveTerm, residueSquareMultiples_card r a hX.le ha,
      Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hX]
    have hnonneg : 0 ≤ ((residueClassFour r (X / (a : ℝ)^2)).card : ℝ) := by positivity
    rw [abs_of_nonneg hnonneg]
    have habs : |(μ a : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)
    have hY : 0 ≤ X / (a : ℝ)^2 := by positivity
    apply (div_le_iff₀ hX).mpr
    calc
      _ ≤ ((residueClassFour r (X / (a : ℝ)^2)).card : ℝ) :=
        mul_le_of_le_one_left (Nat.cast_nonneg _) habs
      _ ≤ X / (a : ℝ)^2 := residueClassFour_card_le r hY
      _ = _ := by ring
  · simp [squarefreeSieveTerm, residueSquareMultiples_card_zero hr ha]

private theorem tendsto_squarefreeSieveTerm (r a : ℕ) (hr₀ : 0 < r) (hr₄ : r < 4) (hr : Odd r) :
    Tendsto (fun X => squarefreeSieveTerm r X a) atTop (𝓝 (oddMoebiusTerm a / 4)) := by
  by_cases ha : Odd a
  · have ha' : 0 < (a : ℝ)^2 := by have := ha.pos; positivity
    have ht : Tendsto (fun X : ℝ => X / (a : ℝ)^2) atTop atTop :=
      (tendsto_div_const_atTop_of_pos ha').mpr tendsto_id
    have hlim := ((tendsto_residueClassFour_card r hr₀ hr₄).comp ht).const_mul (oddMoebiusTerm a)
    rw [show oddMoebiusTerm a / 4 = oddMoebiusTerm a * (1 / 4) by ring]
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    simp only [squarefreeSieveTerm, residueSquareMultiples_card r a hX.le ha, oddMoebiusTerm, if_pos ha,
      Function.comp_apply]
    field_simp [show (a : ℝ) ≠ 0 by exact_mod_cast ha.pos.ne', hX.ne']
  · convert (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0)) using 1
    · funext X
      simp [squarefreeSieveTerm, residueSquareMultiples_card_zero hr ha]
    · simp [oddMoebiusTerm, ha]

/-- Natural density in either odd progression, before evaluating the Möbius series. -/
theorem tendsto_squarefreeResidueClassFour_card (r : ℕ) (hr : r = 1 ∨ r = 3) :
    Tendsto (fun X : ℝ => ((squarefreeResidueClassFour r X).card : ℝ) / X) atTop
      (𝓝 ((∑' a, oddMoebiusTerm a) / 4)) := by
  have hr₀ : 0 < r := by omega
  have hr₄ : r < 4 := by omega
  have hrOdd : Odd r := by rcases hr with rfl | rfl <;> decide
  have hsum : Summable (fun a : ℕ => (1 : ℝ) / (a : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by decide)
  have hlim := tendsto_tsum_of_dominated_convergence hsum (tendsto_squarefreeSieveTerm r · hr₀ hr₄ hrOdd)
    (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX a
        exact squarefreeSieveTerm_bound r a hrOdd hX)
  simp only [squarefreeSieveTerm_tsum, tsum_div_const] at hlim
  exact hlim

end Chowla

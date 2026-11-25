import Chowla.Statement
import Mathlib.Data.Nat.Squarefree

namespace Chowla

open scoped BigOperators

private theorem fundamental_cases {d : ℤ} (hd : IsFundDisc d) :
    (d % 4 = 1 ∧ Squarefree d) ∨
      (∃ e : ℤ, d = 4 * e ∧ e % 4 = 3 ∧ Squarefree e) ∨
      (∃ e : ℤ, d = 8 * e ∧ e % 2 = 1 ∧ Squarefree e) := by
  obtain h | ⟨h4, h2 | h3, hsf⟩ := hd
  · exact .inl h
  · right
    right
    refine ⟨d / 8, by omega, by omega, ?_⟩
    have h : d / 4 = 2 * (d / 8) := by omega
    rw [h] at hsf
    exact hsf.of_mul_right
  · exact .inr (.inl ⟨d / 4, by omega, h3, hsf⟩)

private theorem natAbs_odd {e : ℤ} (he : e % 2 = 1) : Odd e.natAbs := by
  rw [Nat.odd_iff]
  obtain hh | hh := Int.natAbs_eq_iff.mp (rfl : e.natAbs = e.natAbs)
  · omega
  · omega

private theorem dyadicValue_on_unit (d a : ℤ) (ha : IsUnit (a : ZMod d.natAbs)) :
    dyadicCharacter d (a : ZMod d.natAbs) =
      if 8 ∣ d.natAbs then
        if (d / 8) % 4 = 1 then (ZMod.χ₈ (a : ZMod 8) : ℂ)
        else (ZMod.χ₈' (a : ZMod 8) : ℂ)
      else if 4 ∣ d.natAbs then (ZMod.χ₄ (a : ZMod 4) : ℂ) else 1 := by
  have reduction {k : ℕ} (hk : k ∣ d.natAbs) (χ : DirichletCharacter ℂ k) :
      DirichletCharacter.changeLevel hk χ (a : ZMod d.natAbs) = χ (a : ZMod k) := by
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd χ hk ha.unit
    rwa [ha.unit_spec, ZMod.cast_intCast hk a] at h
  unfold dyadicCharacter
  split_ifs with h8 hmode h4
  · rw [reduction]
    rfl
  · rw [reduction]
    rfl
  · rw [reduction]
    rfl
  · exact MulChar.one_apply ha

private theorem odd_primeFactors (m k : ℕ) (hm : Odd m)
    (hk : k = 1 ∨ k = 4 ∨ k = 8) :
    (k * m).primeFactors.erase 2 = m.primeFactors := by
  have htwo : 2 ∉ m.primeFactors := by
    intro h
    have := Nat.dvd_of_mem_primeFactors h
    have := Nat.odd_iff.mp hm
    omega
  obtain rfl | rfl | rfl := hk
  · simpa using Finset.erase_eq_of_notMem htwo
  · have hk4 : (4 : ℕ).primeFactors = {2} := by decide +kernel
    rw [Nat.primeFactors_mul (by decide) hm.pos.ne', hk4]
    ext p
    by_cases hp : p = 2 <;> simp [hp, htwo]
  · have hk8 : (8 : ℕ).primeFactors = {2} := by decide +kernel
    rw [Nat.primeFactors_mul (by decide) hm.pos.ne', hk8]
    ext p
    by_cases hp : p = 2 <;> simp [hp, htwo]

private theorem jacobiSym_finset_prod (a : ℤ) (s : Finset ℕ)
    (h : ∀ q ∈ s, q ≠ 0) :
    jacobiSym a (∏ q ∈ s, q) = ∏ q ∈ s, jacobiSym a q := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hp' : p ≠ 0 := h _ (Finset.mem_insert_self _ _)
    have hs : ∀ q ∈ s, q ≠ 0 := fun q hq => h _ (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hp, Finset.prod_insert hp,
      jacobiSym.mul_right' a hp' (Finset.prod_ne_zero_iff.mpr hs), ih hs]

/-- Evaluation at a unit separates the dyadic factor and the Jacobi symbol for the odd part. -/
theorem chi_apply_unit (d a : ℤ) (k m : ℕ) (hd : d.natAbs = k * m)
    (hk : k = 1 ∨ k = 4 ∨ k = 8) (hodd : Odd m) (hsf : Squarefree m)
    (ha : IsUnit (a : ZMod d.natAbs)) :
    chi d (a : ZMod d.natAbs) = dyadicCharacter d (a : ZMod d.natAbs) * (jacobiSym a m : ℂ) := by
  classical
  let eval : DirichletCharacter ℂ d.natAbs →* ℂ :=
    { toFun := fun ψ => ψ (a : ZMod d.natAbs)
      map_one' := MulChar.one_apply ha
      map_mul' := fun ψ ψ' => MulChar.mul_apply ψ ψ' _ }
  let factors (p : ℕ) : DirichletCharacter ℂ d.natAbs :=
    if hp : p.Prime ∧ p ∣ d.natAbs then
      letI : Fact p.Prime := ⟨hp.1⟩
      DirichletCharacter.changeLevel hp.2
        ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
    else 1
  unfold chi
  rw [MulChar.mul_apply]
  apply congrArg (dyadicCharacter d (a : ZMod d.natAbs) * ·)
  change eval (∏ q ∈ d.natAbs.primeFactors.erase 2, factors q) = _
  rw [map_prod, show d.natAbs.primeFactors.erase 2 = m.primeFactors by
    rw [hd, odd_primeFactors m k hodd hk]]
  conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hsf, jacobiSym_finset_prod a _
    (fun q hq => (Nat.prime_of_mem_primeFactors hq).ne_zero)]
  rw [Int.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hP : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdiv : p ∣ d.natAbs := hd ▸ dvd_trans (Nat.dvd_of_mem_primeFactors hp) (dvd_mul_left m k)
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd
    (letI : Fact p.Prime := ⟨hP⟩
     (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) hdiv ha.unit
  simp only [ha.unit_spec, ZMod.cast_intCast hdiv] at h
  letI : Fact p.Prime := ⟨hP⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym p a]
  change eval (factors p) = (legendreSym p a : ℂ)
  simpa only [eval, MonoidHom.coe_mk, OneHom.coe_mk, factors, dif_pos (And.intro hP hdiv)] using h

private theorem natAbs_factor (d e : ℤ) (k : ℕ) (hd : d = (k : ℤ) * e) :
    d.natAbs = k * e.natAbs := by
  rw [hd, Int.natAbs_mul, Int.natAbs_natCast]

private theorem not_two_dvd_of_odd {m : ℕ} (hm : Odd m) : ¬ 2 ∣ m := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.odd_iff.mp hm]
  decide

/-- The quadratic character's value at the prime 2, including at even discriminants. -/
theorem chi_two (d : ℤ) (hd : IsFundDisc d) :
    chi d 2 = if d % 2 = 0 then 0 else if d % 8 = 1 ∨ d % 8 = 7 then 1 else -1 := by
  by_cases hEven : d % 2 = 0
  · simp only [if_pos hEven]
    have hdiv : 2 ∣ d.natAbs := Int.natCast_dvd.mp (Int.dvd_of_emod_eq_zero hEven)
    have hnonunit : ¬ IsUnit ((2 : ℕ) : ZMod d.natAbs) := by
      rw [ZMod.isUnit_iff_coprime, Nat.prime_two.coprime_iff_not_dvd, not_not]
      exact hdiv
    exact MulChar.map_nonunit (chi d) hnonunit
  · simp only [if_neg hEven]
    have hOdd : d % 2 = 1 := by omega
    have hodd := natAbs_odd hOdd
    have hsf : Squarefree d.natAbs := Int.squarefree_natAbs.mpr <|
      (hd.resolve_right fun h => hEven (by have := h.1; omega)).2
    have hcast : ((2 : ℤ) : ZMod d.natAbs) = (2 : ZMod d.natAbs) := by norm_num
    have hunit : IsUnit ((2 : ℤ) : ZMod d.natAbs) := by
      rw [hcast]
      change IsUnit ((2 : ℕ) : ZMod d.natAbs)
      rw [ZMod.isUnit_iff_coprime, Nat.prime_two.coprime_iff_not_dvd]
      exact not_two_dvd_of_odd hodd
    have h4 : ¬ 4 ∣ d.natAbs :=
      fun h => not_two_dvd_of_odd hodd (dvd_trans (by decide : 2 ∣ 4) h)
    have h8 : ¬ 8 ∣ d.natAbs :=
      fun h => not_two_dvd_of_odd hodd (dvd_trans (by decide : 2 ∣ 8) h)
    rw [← hcast, chi_apply_unit d 2 1 d.natAbs (by simp) (.inl rfl) hodd hsf hunit,
      dyadicValue_on_unit d 2 hunit, if_neg h8, if_neg h4, one_mul,
      jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight, Nat.odd_iff.mp hodd]
    have hmod : (d.natAbs % 8 = 1 ∨ d.natAbs % 8 = 7) ↔
        (d % 8 = 1 ∨ d % 8 = 7) := by
      obtain hs | hs := Int.natAbs_eq_iff.mp (rfl : d.natAbs = d.natAbs)
      · omega
      · omega
    simp only [one_ne_zero, if_false, hmod]
    by_cases h : d % 8 = 1 ∨ d % 8 = 7 <;> simp [h]

private theorem dyadic_sign_mul {e : ℤ} (he : e % 2 = 1) :
    ((if e % 4 = 1 then 1 else -1) : ℤ) * ZMod.χ₄ (e.natAbs : ZMod 4) =
      if e < 0 then -1 else 1 := by
  simp only [ZMod.χ₄_nat_eq_if_mod_four, Nat.odd_iff.mp (natAbs_odd he), Nat.one_ne_zero, if_false]
  have hs₀ : 0 ≤ e → (e % 4 = 1 ↔ e.natAbs % 4 = 1) := by
    intro hn
    have heq := Int.natAbs_of_nonneg hn
    omega
  have hs₁ : e < 0 → (e % 4 = 1 ↔ ¬ e.natAbs % 4 = 1) := by
    intro hn
    obtain h | h := Int.natAbs_eq_iff.mp (rfl : e.natAbs = e.natAbs)
    · omega
    · omega
  by_cases hs : e < 0
  · simp only [if_pos hs, hs₁ hs]
    by_cases h : e.natAbs % 4 = 1 <;> simp [h]
  · simp only [if_neg hs, hs₀ (le_of_not_gt hs)]
    by_cases h : e.natAbs % 4 = 1 <;> simp [h]

private theorem chi_neg_one_of_core (d e : ℤ) (k : ℕ) (hd : d = (k : ℤ) * e)
    (hk : k = 1 ∨ k = 4 ∨ k = 8) (he : e % 2 = 1) (hsf : Squarefree e)
    (hvalue : dyadicCharacter d ((-1 : ℤ) : ZMod d.natAbs) =
      ((if e % 4 = 1 then 1 else -1 : ℤ) : ℂ)) :
    chi d (-1) = if d < 0 then -1 else 1 := by
  have hunit : IsUnit ((-1 : ℤ) : ZMod d.natAbs) := by simp
  have h := chi_apply_unit d (-1) k e.natAbs (natAbs_factor d e k hd) hk
    (natAbs_odd he) (Int.squarefree_natAbs.mpr hsf) hunit
  rw [hvalue, jacobiSym.at_neg_one (natAbs_odd he), ← Int.cast_mul, dyadic_sign_mul he] at h
  have hk₀ : 0 < (k : ℤ) := by
    rcases hk with rfl | rfl | rfl <;> decide
  have hsign : d < 0 ↔ e < 0 := by
    rw [hd]
    refine ⟨fun h => ?_, mul_neg_of_pos_of_neg hk₀⟩
    rcases mul_neg_iff.mp h with h | h
    · exact h.2
    · exact (hk₀.not_gt h.1).elim
  by_cases hs : e < 0 <;> simpa [hsign, hs] using h

/-- The parity of the primitive quadratic character is the sign of its discriminant. -/
theorem chi_neg_one (d : ℤ) (hd : IsFundDisc d) :
    chi d (-1) = if d < 0 then -1 else 1 := by
  have hunit : IsUnit ((-1 : ℤ) : ZMod d.natAbs) := by simp
  have hv := dyadicValue_on_unit d (-1) hunit
  obtain ⟨h4, hsf⟩ | ⟨e, hde, hmod, hsf⟩ | ⟨e, hde, hmod, hsf⟩ := fundamental_cases hd
  · have he : d % 2 = 1 := by omega
    have hdiv4 : ¬ 4 ∣ d.natAbs :=
      fun h => not_two_dvd_of_odd (natAbs_odd he) (dvd_trans (by decide : 2 ∣ 4) h)
    have hdiv8 : ¬ 8 ∣ d.natAbs :=
      fun h => not_two_dvd_of_odd (natAbs_odd he) (dvd_trans (by decide : 2 ∣ 8) h)
    apply chi_neg_one_of_core d d 1 (by simp) (.inl rfl) he hsf
    simpa [hdiv8, hdiv4, h4] using hv
  · have he : e % 2 = 1 := by omega
    have hfac := natAbs_factor d e 4 hde
    have hdiv4 : 4 ∣ d.natAbs := hfac ▸ dvd_mul_right 4 e.natAbs
    have hdiv8 : ¬ 8 ∣ d.natAbs := by
      have := Nat.odd_iff.mp (natAbs_odd he)
      omega
    have htable : ZMod.χ₄ ((-1 : ℤ) : ZMod 4) = -1 := by decide +kernel
    apply chi_neg_one_of_core d e 4 hde (.inr (.inl rfl)) he hsf
    simpa [hdiv8, hdiv4, hmod, htable] using hv
  · have hfac := natAbs_factor d e 8 hde
    have hdiv8 : 8 ∣ d.natAbs := hfac ▸ dvd_mul_right 8 e.natAbs
    have hquot : d / 8 = e := by omega
    have htable : ZMod.χ₈ ((-1 : ℤ) : ZMod 8) = 1 := by decide +kernel
    have htable' : ZMod.χ₈' ((-1 : ℤ) : ZMod 8) = -1 := by decide +kernel
    apply chi_neg_one_of_core d e 8 hde (.inr (.inr rfl)) hmod hsf
    by_cases he : e % 4 = 1 <;> simpa [hdiv8, hquot, he, htable, htable'] using hv

private theorem jacobiSym_odd_signed (e : ℤ) (p : ℕ) (he : e % 2 = 1) (hp : Odd p) :
    jacobiSym e p = (if e % 4 = 1 then 1 else ZMod.χ₄ (p : ZMod 4)) * jacobiSym p e.natAbs := by
  let m := e.natAbs
  have hm := Nat.odd_iff.mp (natAbs_odd he)
  have hp₂ := Nat.odd_iff.mp hp
  have hrec := (jacobiSym.quadratic_reciprocity_if hm hp₂).symm
  have hχ₄ : ZMod.χ₄ (p : ZMod 4) = if p % 4 = 1 then 1 else -1 := by
    simp only [ZMod.χ₄_nat_eq_if_mod_four, hp₂, Nat.one_ne_zero, if_false]
  obtain h | h := Int.natAbs_eq_iff.mp (rfl : e.natAbs = e.natAbs)
  · have hmod : e % 4 = 1 ↔ m % 4 = 1 := by dsimp [m]; omega
    change jacobiSym e p = (if e % 4 = 1 then 1 else ZMod.χ₄ (p : ZMod 4)) * jacobiSym p m
    simp only [hmod, hχ₄]
    conv_lhs => rw [show e = (m : ℤ) from h, hrec]
    rcases Nat.odd_mod_four_iff.mp hm with hm₁ | hm₃
    · rcases Nat.odd_mod_four_iff.mp hp₂ with hp₁ | hp₃
      · simp [m, hm₁, hp₁]
      · simp [m, hm₁, hp₃]
    · rcases Nat.odd_mod_four_iff.mp hp₂ with hp₁ | hp₃
      · simp [m, hm₃, hp₁]
      · simp [m, hm₃, hp₃]
  · have hmod : e % 4 = 1 ↔ m % 4 = 3 := by dsimp [m]; omega
    change jacobiSym e p = (if e % 4 = 1 then 1 else ZMod.χ₄ (p : ZMod 4)) * jacobiSym p m
    simp only [hmod, hχ₄]
    conv_lhs => rw [show e = -(m : ℤ) from h, jacobiSym.neg _ hp, hrec, hχ₄]
    rcases Nat.odd_mod_four_iff.mp hm with hm₁ | hm₃
    · rcases Nat.odd_mod_four_iff.mp hp₂ with hp₁ | hp₃
      · simp [m, hm₁, hp₁]
      · simp [m, hm₁, hp₃]
    · rcases Nat.odd_mod_four_iff.mp hp₂ with hp₁ | hp₃
      · simp [m, hm₃, hp₁]
      · simp [m, hm₃, hp₃]

/-- Quadratic reciprocity identifies the local construction with the Kronecker symbol at odd primes. -/
theorem chi_odd_prime (d : ℤ) (hd : IsFundDisc d) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    chi d (p : ZMod d.natAbs) = (legendreSym p d : ℂ) := by
  have hpP : p.Prime := Fact.out
  have hpOdd := hpP.eq_two_or_odd'.resolve_left hp
  have hp₂ := Nat.odd_iff.mp hpOdd
  have hu : IsUnit (p : ZMod d.natAbs) ↔ ¬ p ∣ d.natAbs :=
    (ZMod.isUnit_iff_coprime p _).trans hpP.coprime_iff_not_dvd
  by_cases hdiv : p ∣ d.natAbs
  · rw [MulChar.map_nonunit _ (hu.not.mpr (not_not.mpr hdiv))]
    have hχ : legendreSym p d = 0 := (legendreSym.eq_zero_iff p d).mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mpr (Int.natCast_dvd.mpr hdiv))
    simp [hχ]
  · have hpU : IsUnit ((p : ℤ) : ZMod d.natAbs) := by simpa only [Int.cast_natCast] using hu.mpr hdiv
    have hv := dyadicValue_on_unit d p hpU
    have hcast : chi d ((p : ℤ) : ZMod d.natAbs) = chi d (p : ZMod d.natAbs) := by
      rw [Int.cast_natCast]
    rw [← hcast, jacobiSym.legendreSym.to_jacobiSym]
    obtain ⟨h₄, hsf⟩ | ⟨e, hde, hmod, hsf⟩ | ⟨e, hde, hmod, hsf⟩ := fundamental_cases hd
    · have he : d % 2 = 1 := by omega
      have hodd := natAbs_odd he
      have hd₂ := not_two_dvd_of_odd hodd
      have hd₄ : ¬ 4 ∣ d.natAbs := fun h => hd₂ (dvd_trans (by decide : 2 ∣ 4) h)
      have hd₈ : ¬ 8 ∣ d.natAbs := fun h => hd₂ (dvd_trans (by decide : 2 ∣ 8) h)
      rw [chi_apply_unit d p 1 d.natAbs (by simp) (.inl rfl) hodd
        (Int.squarefree_natAbs.mpr hsf) hpU, hv, if_neg hd₈, if_neg hd₄, one_mul,
        jacobiSym_odd_signed d p he hpOdd, if_pos h₄, one_mul]
    · have he : e % 2 = 1 := by omega
      have hodd := natAbs_odd he
      have hfac := natAbs_factor d e 4 hde
      have hd₄ : 4 ∣ d.natAbs := hfac ▸ dvd_mul_right 4 e.natAbs
      have hd₈ : ¬ 8 ∣ d.natAbs := by have := Nat.odd_iff.mp hodd; omega
      have h₄ : d % 4 = 0 := by omega
      rw [chi_apply_unit d p 4 e.natAbs hfac (.inr (.inl rfl)) hodd
        (Int.squarefree_natAbs.mpr hsf) hpU, hv, if_neg hd₈, if_pos hd₄,
        ← jacobiSym.div_four_left h₄ hp₂, show d / 4 = e by omega,
        jacobiSym_odd_signed e p he hpOdd, if_neg (by omega : e % 4 ≠ 1), Int.cast_mul, Int.cast_natCast]
    · have hodd := natAbs_odd hmod
      have hfac := natAbs_factor d e 8 hde
      have hd₈ : 8 ∣ d.natAbs := hfac ▸ dvd_mul_right 8 e.natAbs
      have h₄ : d % 4 = 0 := by omega
      rw [chi_apply_unit d p 8 e.natAbs hfac (.inr (.inr rfl)) hodd
        (Int.squarefree_natAbs.mpr hsf) hpU, hv, if_pos hd₈, show d / 8 = e by omega,
        ← jacobiSym.div_four_left h₄ hp₂, show d / 4 = 2 * e by omega,
        jacobiSym.mul_left, jacobiSym.at_two hpOdd, jacobiSym_odd_signed e p hmod hpOdd]
      by_cases he : e % 4 = 1
      · simp only [he, if_true, one_mul, Int.cast_mul, Int.cast_natCast]
      · simp only [he, if_false, Int.cast_mul, Int.cast_natCast]
        have hmul := ZMod.χ₈'_int_eq_χ₄_mul_χ₈ (p : ℤ)
        simp only [Int.cast_natCast] at hmul
        rw [hmul, Int.cast_mul]
        ring

private theorem dyadic_coprime_odd {k m : ℕ} (hk : k = 1 ∨ k = 4 ∨ k = 8)
    (hm : Odd m) : k.Coprime m := by
  have htwo := Nat.prime_two.coprime_iff_not_dvd.mpr (not_two_dvd_of_odd hm)
  rcases hk with rfl | rfl | rfl
  · exact Nat.coprime_one_left _
  · exact htwo.pow_left 2
  · exact htwo.pow_left 3

private theorem zmod_natCast_eq {a b k : ℕ} (h : a ≡ b [MOD k]) :
    (a : ZMod k) = (b : ZMod k) :=
  (ZMod.natCast_eq_natCast_iff a b k).2 h

private theorem unit_at_one {a n : ℕ} (h : a ≡ 1 [MOD n]) : IsUnit (a : ZMod n) := by
  simpa only [zmod_natCast_eq h, Nat.cast_one] using (isUnit_one : IsUnit (1 : ZMod n))

private theorem jacobiSym_eq_one_of_modEq {a m : ℕ} (h : a ≡ 1 [MOD m]) :
    jacobiSym (a : ℤ) m = 1 := by
  rw [← jacobiSym.one_left m]
  apply jacobiSym.mod_left'
  change a % m = 1 % m at h
  exact_mod_cast h

private theorem factorsThrough_eq_one_of_modEq {n c : ℕ} {χ : DirichletCharacter ℂ n}
    (hf : χ.FactorsThrough c) {a : ℕ} (hunit : IsUnit (a : ZMod n)) (h : a ≡ 1 [MOD c]) :
    χ (a : ZMod n) = 1 := by
  obtain ⟨hc, ψ, hχ⟩ := hf
  rw [hχ]
  have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ hc hunit.unit
  rwa [hunit.unit_spec, ZMod.cast_natCast hc, zmod_natCast_eq h, Nat.cast_one, map_one] at h1

private theorem dyadic_eq_one_of_modEq (d : ℤ) {k m : ℕ} (hN : d.natAbs = k * m)
    (hk : k = 1 ∨ k = 4 ∨ k = 8) (hm : Odd m) {a : ℕ}
    (hunit : IsUnit (a : ZMod d.natAbs)) (ha : a ≡ 1 [MOD k]) :
    dyadicCharacter d (a : ZMod d.natAbs) = 1 := by
  have h := dyadicValue_on_unit d (a : ℤ) (by simpa only [Int.cast_natCast] using hunit)
  simp only [Int.cast_natCast] at h
  have hm₂ := Nat.odd_iff.mp hm
  rcases hk with rfl | rfl | rfl
  · have h₄ : ¬ 4 ∣ d.natAbs := by omega
    have h₈ : ¬ 8 ∣ d.natAbs := by omega
    simpa [h₈, h₄] using h
  · have h₄ : 4 ∣ d.natAbs := hN ▸ dvd_mul_right 4 m
    have h₈ : ¬ 8 ∣ d.natAbs := by omega
    simpa only [if_neg h₈, if_pos h₄, zmod_natCast_eq ha, Nat.cast_one, map_one, Int.cast_one] using h
  · have h₈ : 8 ∣ d.natAbs := hN ▸ dvd_mul_right 8 m
    simpa only [if_pos h₈, zmod_natCast_eq ha, Nat.cast_one, map_one, Int.cast_one, ite_self] using h

private theorem odd_prime_dvd_of_factorsThrough (d : ℤ) {c k m p : ℕ}
    (hN : d.natAbs = k * m) (hk : k = 1 ∨ k = 4 ∨ k = 8)
    (hm : Odd m) (hsf : Squarefree m) (hf : (chi d).FactorsThrough c)
    (hp : p.Prime) (hpd : p ∣ m) : p ∣ c := by
  by_contra hpc
  let j := m / p
  have hjp : j * p = m := Nat.div_mul_cancel hpd
  have hj₀ : j ≠ 0 := by
    intro h
    have := hm.pos.ne'
    simp [h] at hjp
    exact this hjp.symm
  have hpj : ¬ p ∣ j := by
    intro h
    have h₂ : p * p ∣ j * p := Nat.mul_dvd_mul h (dvd_refl _)
    exact (Nat.squarefree_iff_prime_squarefree.mp hsf p hp) (hjp ▸ h₂)
  have hp₂ : p ≠ 2 := by
    intro he
    exact not_two_dvd_of_odd hm (he ▸ hpd)
  have hcop : (k * j).Coprime p := Nat.Coprime.mul_left
    ((dyadic_coprime_odd hk hm).of_dvd_right hpd)
    (hp.coprime_iff_not_dvd.mpr hpj).symm
  have hdec : (k * j) * p = d.natAbs := by rw [mul_assoc, hjp, hN]
  have hc : c ∣ k * j := ((hp.coprime_iff_not_dvd.mpr hpc).symm).dvd_of_dvd_mul_right (hdec ▸ hf.dvd)
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := ZMod p) (by
    rwa [ZMod.ringChar_zmod_n])
  let a₀ := a.val.val
  have ha₀ : (a₀ : ZMod p) = a := by
    exact ZMod.natCast_zmod_val a.val
  obtain ⟨u, hrest, hprime⟩ := Nat.chineseRemainder hcop 1 a₀
  have hpU : (u : ZMod p) = a := (zmod_natCast_eq hprime).trans ha₀
  have hkgood : u.Coprime (k * j) :=
    (ZMod.isUnit_iff_coprime u _).mp (unit_at_one hrest)
  have hpgood : u.Coprime p :=
    (ZMod.isUnit_iff_coprime u _).mp (hpU ▸ a.isUnit)
  have huN := (ZMod.isUnit_iff_coprime u d.natAbs).mpr (hdec ▸ hkgood.mul_right hpgood)
  have hχ₁ := factorsThrough_eq_one_of_modEq hf huN (hrest.of_dvd hc)
  have hχ₂ := chi_apply_unit d u k m hN hk hm hsf (by simpa only [Int.cast_natCast] using huN)
  have hDyad := dyadic_eq_one_of_modEq d hN hk hm huN (hrest.of_dvd (dvd_mul_right k j))
  have hRestJac := jacobiSym_eq_one_of_modEq (hrest.of_dvd (dvd_mul_left j k))
  have hPrimeJac : jacobiSym (u : ℤ) p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    change quadraticChar (ZMod p) ((u : ℤ) : ZMod p) = -1
    rwa [Int.cast_natCast, hpU]
  simp only [Int.cast_natCast] at hχ₂
  rw [hχ₁, hDyad, one_mul, ← hjp, jacobiSym.mul_right' _ hj₀ hp.ne_zero,
    hRestJac, hPrimeJac, one_mul] at hχ₂
  norm_num at hχ₂

private theorem oddPart_dvd_of_factorsThrough (d : ℤ) {c k m : ℕ}
    (hN : d.natAbs = k * m) (hk : k = 1 ∨ k = 4 ∨ k = 8)
    (hm : Odd m) (hsf : Squarefree m) (hf : (chi d).FactorsThrough c) : m ∣ c := by
  rw [← Nat.prod_primeFactors_of_squarefree hsf]
  apply Finset.prod_dvd_of_isRelPrime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp <| (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq
  · intro p hp
    exact odd_prime_dvd_of_factorsThrough d hN hk hm hsf hf
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

private theorem gcd_two_pow_dvd_previous {c r : ℕ} (hr : 0 < r) (hc : ¬2^r ∣ c) :
    c.gcd (2^r) ∣ 2^(r-1) := by
  obtain ⟨i, hir, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_right c (2^r))
  have hir' : i < r := by
    refine lt_of_le_of_ne hir ?_
    intro h
    rw [h] at hi
    exact hc (hi ▸ Nat.gcd_dvd_left c (2^r))
  rw [hi]
  exact pow_dvd_pow 2 (by omega)

private theorem dyadic_witness (d : ℤ) {k m : ℕ} (hN : d.natAbs = k * m)
    (hk : k = 4 ∨ k = 8) (hm : Odd m) :
    ∃ v : ℕ, v.Coprime k ∧ (v ≡ 1 [MOD k/2]) ∧
      ∀ u : ℕ, (u ≡ v [MOD k]) → IsUnit (u : ZMod d.natAbs) →
        dyadicCharacter d (u : ZMod d.natAbs) = -1 := by
  have hM := Nat.odd_iff.mp hm
  rcases hk with rfl | rfl
  · refine ⟨3, by decide +kernel, by decide +kernel, fun u hU hu => ?_⟩
    have h₄ : 4 ∣ d.natAbs := hN ▸ dvd_mul_right 4 m
    have h₈ : ¬ 8 ∣ d.natAbs := by omega
    have heq : ZMod.χ₄ ((3 : ℕ) : ZMod 4) = -1 := by decide +kernel
    have h := dyadicValue_on_unit d u (by simpa only [Int.cast_natCast] using hu)
    simpa only [Int.cast_natCast, if_neg h₈, if_pos h₄, zmod_natCast_eq hU, heq,
      Int.cast_neg, Int.cast_one] using h
  · refine ⟨5, by decide +kernel, by decide +kernel, fun u hU hu => ?_⟩
    have h₈ : 8 ∣ d.natAbs := hN ▸ dvd_mul_right 8 m
    have heq : ZMod.χ₈ ((5 : ℕ) : ZMod 8) = -1 := by decide +kernel
    have heq' : ZMod.χ₈' ((5 : ℕ) : ZMod 8) = -1 := by decide +kernel
    have h := dyadicValue_on_unit d u (by simpa only [Int.cast_natCast] using hu)
    simpa only [Int.cast_natCast, if_pos h₈, zmod_natCast_eq hU, heq, heq',
      Int.cast_neg, Int.cast_one, ite_self] using h

private theorem dyadic_dvd_of_factorsThrough (d : ℤ) {c k m : ℕ}
    (hN : d.natAbs = k * m) (hk : k = 4 ∨ k = 8)
    (hm : Odd m) (hsf : Squarefree m) (hf : (chi d).FactorsThrough c) : k ∣ c := by
  by_contra hkc
  have hcop : k.Coprime m := dyadic_coprime_odd (.inr hk) hm
  have hhalf : k/2 ∣ k := by rcases hk with rfl | rfl <;> decide
  have hc_gcd : c = (c.gcd k) * (c.gcd m) :=
    ((Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hcop).mpr (hN ▸ hf.dvd)).symm
  have hgcd : c.gcd k ∣ k/2 := by
    rcases hk with rfl | rfl
    · exact gcd_two_pow_dvd_previous (r := 2) (by decide) hkc
    · exact gcd_two_pow_dvd_previous (r := 3) (by decide) hkc
  have hc : c ∣ (k/2)*m := hc_gcd.symm ▸ Nat.mul_dvd_mul hgcd (Nat.gcd_dvd_right c m)
  obtain ⟨v, hv, hv₁, hneg⟩ := dyadic_witness d hN hk hm
  obtain ⟨u, hukt, hum⟩ := Nat.chineseRemainder hcop v 1
  have hu₁ : u ≡ 1 [MOD c] := by
    apply Nat.ModEq.of_dvd hc
    apply (Nat.modEq_and_modEq_iff_modEq_mul (hcop.of_dvd_left hhalf)).mp
    exact ⟨(hukt.of_dvd hhalf).trans hv₁, hum⟩
  have huK : u.Coprime k := by
    rw [← ZMod.isUnit_iff_coprime, zmod_natCast_eq hukt, ZMod.isUnit_iff_coprime]
    exact hv
  have huM : u.Coprime m :=
    (ZMod.isUnit_iff_coprime u _).mp (unit_at_one hum)
  have hu : IsUnit (u : ZMod d.natAbs) := by
    rw [hN, ZMod.isUnit_iff_coprime]
    exact huK.mul_right huM
  have hχ₁ := factorsThrough_eq_one_of_modEq hf hu hu₁
  have hχ₂ := chi_apply_unit d u k m hN (.inr hk) hm hsf
    (by simpa only [Int.cast_natCast] using hu)
  simp only [Int.cast_natCast] at hχ₂
  rw [hχ₁, hneg u hukt hu, jacobiSym_eq_one_of_modEq hum, Int.cast_one, mul_one] at hχ₂
  norm_num at hχ₂

private theorem primitive_of_odd_core (d : ℤ) (k m : ℕ) (hN : d.natAbs = k * m)
    (hk : k = 1 ∨ k = 4 ∨ k = 8) (hm : Odd m) (hsf : Squarefree m) :
    (chi d).IsPrimitive := by
  let c := (chi d).conductor
  have hf : (chi d).FactorsThrough c := (chi d).factorsThrough_conductor
  have hmD : m ∣ c := oddPart_dvd_of_factorsThrough d hN hk hm hsf hf
  have hkD : k ∣ c := by
    rcases hk with rfl | hk
    · exact one_dvd c
    · exact dyadic_dvd_of_factorsThrough d hN hk hm hsf hf
  change c = d.natAbs
  apply Nat.dvd_antisymm hf.dvd
  rw [hN]
  exact (dyadic_coprime_odd hk hm).mul_dvd_of_dvd_of_dvd hkD hmD

/-- The local quadratic character of a fundamental discriminant is primitive. -/
theorem chi_primitive (d : ℤ) (hd : IsFundDisc d) : (chi d).IsPrimitive := by
  obtain ⟨h₄, hsf⟩ | ⟨e, hde, hmod, hsf⟩ | ⟨e, hde, hmod, hsf⟩ := fundamental_cases hd
  · exact primitive_of_odd_core d 1 d.natAbs (by simp) (.inl rfl) (natAbs_odd (by omega))
      (Int.squarefree_natAbs.mpr hsf)
  · exact primitive_of_odd_core d 4 e.natAbs (natAbs_factor d e 4 hde) (.inr (.inl rfl))
      (natAbs_odd (by omega)) (Int.squarefree_natAbs.mpr hsf)
  · exact primitive_of_odd_core d 8 e.natAbs (natAbs_factor d e 8 hde) (.inr (.inr rfl))
      (natAbs_odd hmod) (Int.squarefree_natAbs.mpr hsf)

end Chowla

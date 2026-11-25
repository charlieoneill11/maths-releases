import Legendre.Cited

namespace Legendre

private def primesThrough (n : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter Nat.Prime

private theorem mem_primesThrough {n p : ℕ} : p ∈ primesThrough n ↔ p.Prime ∧ p ≤ n := by
  simp [primesThrough, and_comm]

private theorem card_primesThrough (n : ℕ) : (primesThrough n).card = Nat.primeCounting n := by
  exact (Nat.count_eq_card_filter_range Nat.Prime (n + 1)).symm

/-- Montgomery–Vaughan's bound with one allowance for the left endpoint. -/
theorem primeCount_bound_closed (h : CitedFacts) {s : Finset ℕ} {a b : ℝ} (ha : 0 < a)
    (hlen : 1 < b - a) (hs : ∀ p ∈ s, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b) :
    (s.card : ℝ) ≤ 2 * (b - a) / Real.log (b - a) + 1 := by
  have hab : a ≤ b := by linarith
  have hb : 0 ≤ b := ha.le.trans hab
  let lo := primesThrough ⌊a⌋₊
  let hi := primesThrough ⌊b⌋₊
  have hsub : lo ⊆ hi := by
    intro p hp
    obtain ⟨hp', hle⟩ := mem_primesThrough.mp hp
    exact mem_primesThrough.mpr ⟨hp', hle.trans (Nat.floor_mono hab)⟩
  have hs' : s ⊆ insert ⌊a⌋₊ (hi \ lo) := by
    intro p hps
    obtain ⟨hp, hpa, hpb⟩ := hs p hps
    by_cases hplo : p ∈ lo
    · have hple : (p : ℝ) ≤ a :=
        (Nat.cast_le.mpr (mem_primesThrough.mp hplo).2).trans (Nat.floor_le ha.le)
      have heq : ⌊a⌋₊ = p := by rw [le_antisymm hpa hple, Nat.floor_natCast]
      rw [heq]
      exact Finset.mem_insert_self _ _
    · have hphi : p ∈ hi := mem_primesThrough.mpr ⟨hp, (Nat.le_floor_iff hb).mpr hpb⟩
      exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hphi, hplo⟩)
  have hc : (hi \ lo).card = primeCountIn a (b - a) := by
    rw [Finset.card_sdiff_of_subset hsub, primeCountIn, show a + (b - a) = b by ring]
    simp only [hi, lo, card_primesThrough]
  have hout : s.card ≤ primeCountIn a (b - a) + 1 := by
    rw [← hc]
    exact (Finset.card_le_card hs').trans (Finset.card_insert_le _ _)
  have hreal : (s.card : ℝ) ≤ (primeCountIn a (b - a) : ℝ) + 1 := by exact_mod_cast hout
  exact hreal.trans (add_le_add_left (h.montgomeryVaughan a (b - a) ha hlen) 1)

end Legendre

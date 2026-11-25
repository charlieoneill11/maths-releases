import HadwigerNelson.Packing.Parameters
import HadwigerNelson.Packing.CapRuntime
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.NormNum

namespace HadwigerNelson.Packing

private theorem annulus_le_of_test {a b : ℚ} {k : ℕ} (A : ℕ) (h : annulusTest a b k) :
    annulusCap (a:ℝ) (b:ℝ) A ≤ k := by
  classical
  simp only [annulusTest,decide_eq_true_eq] at h
  unfold annulusCap
  dsimp only
  have yes : 4 ≤ k ∧ k ≤ 127 ∧ annulusCosine (a:ℝ) (b:ℝ) <
      1-(44/(7*(k+1:ℕ)):ℝ)^2/2+(44/(7*(k+1:ℕ)):ℝ)^4/24-(44/(7*(k+1:ℕ)):ℝ)^6/720 := by
    refine ⟨h.1,h.2.1,?_⟩
    unfold annulusCosine
    have cast := (Rat.cast_lt (K:=ℝ)).mpr h.2.2
    push_cast at cast
    simpa only [Nat.cast_add,Nat.cast_one] using cast
  rw [dif_pos ⟨k,yes⟩]
  exact Nat.find_min' _ yes

private noncomputable def candidates (M A : ℕ) : Set ℕ :=
  {b | b = A ∨ b = annulusCap 1 (M/100:ℝ) A ∨
    ∃ j : ℕ, 11 ≤ j ∧ 10*j < M ∧ b = annulusCap 1 (j/10:ℝ) A + annulusCap (j/10:ℝ) (M/100:ℝ) A}

private theorem checkedRing_sound (M A b : ℕ) (h : checkedRing M = some b) :
    sInf (candidates M A) ≤ b := by
  unfold checkedRing at h
  dsimp only at h
  split at h
  · contradiction
  next k _ =>
    split at h
    next pass =>
      cases h
      have c : annulusCap 1 (M/100:ℝ) A ≤ b := by simpa using annulus_le_of_test A pass
      exact (Nat.sInf_le (s:=candidates M A) (Or.inr (Or.inl rfl))).trans c
    next => contradiction
  next j k i _ =>
    split at h
    next pass =>
      cases h
      obtain ⟨hj,hm,lo,hi⟩ := pass
      have l : annulusCap 1 (j/10:ℝ) A ≤ k := by simpa using annulus_le_of_test A lo
      have u : annulusCap (j/10:ℝ) (M/100:ℝ) A ≤ i := by simpa using annulus_le_of_test A hi
      exact (Nat.sInf_le (s:=candidates M A) (Or.inr (Or.inr ⟨j,hj,hm,rfl⟩))).trans (Nat.add_le_add l u)
    next => contradiction

attribute [local irreducible] ringTable annulusHints checkedRing

/-- A rechecked ring witness from the cache is a rigorous upper bound. When there is no
witness the executable cap falls back to the floor of the disjoint-disc area bound. -/
theorem neighbourCap_le_capUpper (ρ t : ℚ) :
    neighbourCap (ρ:ℝ) (t:ℝ) ≤ capUpper ρ t := by
  classical
  let A := ⌊(1+2*t/ρ)^2⌋₊-1
  let M := ⌈100*t/ρ⌉₊
  have disk : ⌊(1+2*(t:ℝ)/(ρ:ℝ))^2⌋₊-1 = A := by
    dsimp [A]
    rw [←Int.floor_toNat,←Int.floor_toNat,←Rat.floor_cast (α:=ℝ) ((1+2*t/ρ)^2)]
    push_cast
    rfl
  have top : ⌈100*(t:ℝ)/(ρ:ℝ)⌉₊ = M := by
    dsimp [M]
    rw [←Int.ceil_toNat,←Int.ceil_toNat,←Rat.ceil_cast (α:=ℝ) (100*t/ρ)]
    push_cast
    rfl
  have castle : (t:ℝ) ≤ (ρ:ℝ) ↔ t ≤ ρ := by exact_mod_cast Iff.rfl
  unfold neighbourCap capUpper
  dsimp only
  by_cases hsmall : t ≤ ρ
  · rw [if_pos hsmall,if_pos (castle.mpr hsmall)]
  · rw [if_neg hsmall,if_neg (fun h ↦ hsmall (castle.mp h)),disk,top]
    change sInf (candidates M A) ≤ (match (ringTable[M]?).join with | some k => min A k | none => A)
    have base : sInf (candidates M A) ≤ A := Nat.sInf_le (Or.inl rfl)
    split
    next k h =>
      apply le_min base
      by_cases hm : M < 401
      · have get : ringTable[M]? = some (checkedRing M) := by simp [ringTable,hm]
        rw [get] at h
        exact checkedRing_sound M A k h
      · have get : ringTable[M]? = none := by simp [ringTable,hm]
        simp [get] at h
    next => exact base

end HadwigerNelson.Packing

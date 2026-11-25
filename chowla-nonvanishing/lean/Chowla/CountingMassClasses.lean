import Chowla.CountingDyadic
import Mathlib.Data.Nat.Squarefree

namespace Chowla

open Filter MeasureTheory
open scoped BigOperators Topology

/-- Ranges of the positive odd parameter (m) in the six classes. -/
def ClassCorePred (D : DiscClass) (m : ℕ) : Prop :=
  Odd m ∧ Squarefree m ∧
    match D.2 with
    | .odd => 1 < m ∧ (D.1.value * (m : ℤ)) % 4 = 1
    | .four => (D.1.value * (m : ℤ)) % 4 = 3
    | .eight => True

noncomputable def classCoreCutoff (D : DiscClass) (X : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 ⌊X⌋₊).filter (ClassCorePred D)

private def discFromCore (D : DiscClass) : ℕ ↪ ℤ where
  toFun m := (D.2.kappa : ℤ) * D.1.value * (m : ℤ)
  inj' := by
    intro a b h
    have hk : (D.2.kappa : ℤ) ≠ 0 := by cases D.2 <;> decide
    have hs : D.1.value ≠ 0 := by cases D.1 <;> decide
    exact Int.ofNat.inj (mul_left_cancel₀ (mul_ne_zero hk hs) h)

private theorem discFromCore_abs (D : DiscClass) (m : ℕ) :
    (discFromCore D m).natAbs = D.2.kappa * m := by
  have hsign : D.1.value.natAbs = 1 := by cases D.1 <;> decide
  simp [discFromCore, Int.natAbs_mul, hsign]

private theorem oddPart_discFromCore (D : DiscClass) (m : ℕ) :
    oddPart D (discFromCore D m) = (m : ℝ) := by
  rw [oddPart, discFromCore_abs, Nat.cast_mul, mul_comm, mul_div_cancel_right₀ _ (kappa_pos D).ne']

private theorem discFromCore_property (D : DiscClass) (m : ℕ) (h : ClassCorePred D m) :
    IsFundDisc (discFromCore D m) ∧ 1 < |discFromCore D m| := by
  obtain ⟨hm, hsf, hLocal⟩ := h
  let v := D.1.value * (m : ℤ)
  have hvabs : v.natAbs = m := by
    have hsign : D.1.value.natAbs = 1 := by cases D.1 <;> decide
    simp [v, Int.natAbs_mul, hsign]
  have hv : v % 2 = 1 := Int.odd_iff.mp <| Int.natAbs_odd.mp (hvabs ▸ hm)
  have hvsf : Squarefree v := Int.squarefree_natAbs.mp (hvabs ▸ hsf)
  have h2vsf : Squarefree (2 * v) := by
    apply Int.squarefree_natAbs.mp
    rw [Int.natAbs_mul, hvabs]
    have hcop : (2 : ℕ).Coprime m := Nat.prime_two.coprime_iff_not_dvd.mpr (fun h => by
      have hodd := Nat.odd_iff.mp hm
      omega)
    exact (Nat.squarefree_mul hcop).mpr ⟨Nat.squarefree_two, hsf⟩
  have hmpos := hm.pos
  have habs : |discFromCore D m| = (↑(D.2.kappa * m) : ℤ) := by
    rw [Int.abs_eq_natAbs, discFromCore_abs]
  constructor
  · have heq : discFromCore D m = (D.2.kappa : ℤ) * v := by
      simp only [discFromCore, Function.Embedding.coeFn_mk, v, mul_assoc]
    rw [heq]
    cases hT : D.2 with
    | odd =>
      simp only [hT] at hLocal
      have hd4 : v % 4 = 1 := hLocal.2
      simp only [DiscType.kappa, Nat.cast_one, one_mul, IsFundDisc]
      exact Or.inl ⟨hd4, hvsf⟩
    | four =>
      have hd4 : v % 4 = 3 := by simpa only [hT] using hLocal
      simp only [DiscType.kappa, Nat.cast_ofNat, IsFundDisc]
      refine Or.inr ⟨by omega, Or.inr (by omega), ?_⟩
      have heq4 : (4 * v) / 4 = v := by omega
      rw [heq4]
      exact hvsf
    | eight =>
      simp only [DiscType.kappa, Nat.cast_ofNat, IsFundDisc]
      refine Or.inr ⟨by omega, Or.inl (by omega), ?_⟩
      have heq4 : (8 * v) / 4 = 2 * v := by omega
      rw [heq4]
      exact h2vsf
  · rw [habs]
    cases hT : D.2 with
    | odd =>
      simp only [hT] at hLocal
      have hm' : 1 < m := hLocal.1
      simpa [DiscType.kappa] using (show (1 : ℤ) < (m : ℤ) by exact_mod_cast hm')
    | four =>
      change (1 : ℤ) < ((4 * m : ℕ) : ℤ)
      exact_mod_cast (show 1 < 4 * m by omega)
    | eight =>
      change (1 : ℤ) < ((8 * m : ℕ) : ℤ)
      exact_mod_cast (show 1 < 8 * m by omega)

/-- Reindexing a discriminant cutoff by the corresponding positive odd integer. -/
private theorem classDiscs_eq_map_core (D : DiscClass) {X : ℝ} (hX : 0 ≤ X) :
    classDiscs D ((D.2.kappa : ℝ) * X) =
      (classCoreCutoff D X).map (discFromCore D) := by
  classical
  ext d
  rw [mem_classDiscs_iff, mem_discs_iff_abs, Finset.mem_map]
  constructor
  · rintro ⟨⟨hcut, _, _⟩, ⟨m, hm, hsf, hdm, hLocal⟩⟩
    have hdm' : discFromCore D m = d := hdm.symm
    rw [← hdm', Int.abs_eq_natAbs, discFromCore_abs, Int.cast_natCast, Nat.cast_mul] at hcut
    have hcut' := (mul_le_mul_iff_of_pos_left (kappa_pos D)).mp hcut
    refine ⟨m, ?_, hdm'⟩
    have hm' : m ≤ ⌊X⌋₊ := (Nat.le_floor_iff hX).mpr hcut'
    simp only [classCoreCutoff, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hm.pos, hm'⟩, hm, hsf, hLocal⟩
  · rintro ⟨m, hm, rfl⟩
    simp only [classCoreCutoff, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨hsf, habt⟩ := discFromCore_property D m hm.2
    refine ⟨⟨?_, hsf, habt⟩, ⟨m, hm.2.1, hm.2.2.1, rfl, hm.2.2.2⟩⟩
    rw [Int.abs_eq_natAbs, discFromCore_abs, Int.cast_natCast, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left ((Nat.le_floor_iff hX).mp hm.1.2) (kappa_pos D).le

theorem classDiscs_card_eq_core (D : DiscClass) {X : ℝ} (hX : 0 ≤ X) :
    (classDiscs D ((D.2.kappa : ℝ) * X)).card = (classCoreCutoff D X).card := by
  rw [classDiscs_eq_map_core D hX, Finset.card_map]

theorem weightedMass_eq_core (D : DiscClass) (W : ShellWeight) {X : ℝ} (hX : 0 ≤ X) :
    weightedSum D W X (fun _ => 1) =
      ∑ m ∈ classCoreCutoff D (2 * X), W.toFun ((m : ℝ) / X) := by
  classical
  have hcut : 2 * (D.2.kappa : ℝ) * X = (D.2.kappa : ℝ) * (2 * X) := by ring
  rw [weightedSum, hcut, classDiscs_eq_map_core D (by positivity), Finset.sum_map]
  simp only [oddPart_discFromCore, mul_one]

end Chowla

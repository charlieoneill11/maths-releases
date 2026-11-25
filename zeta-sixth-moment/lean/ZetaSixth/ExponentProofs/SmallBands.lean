import ZetaSixth.ExponentProofs.Splits

namespace ZetaSixth.Exponents

open Degrees Identities

private theorem small_j_square_bounds (q : Degrees) (hq : q.Admissible)
    (hς : q.ς < 1 / 8) (hm : q.m ≤ q.sigma / 2 + q.tau) (hj : q.j ≤ 2 * q.tau) :
    0 < q.b - q.j - q.r ∧ 0 < q.P0 ∧ 0 < q.P2 ∧ 0 < q.P3 ∧
      1 - 9 * q.ς + 5 * q.g + 10 * q.r + 36 / 5 * q.tail + 2 * (q.Z + q.E) ≤ 4 * q.P1 := by
  rcases hq with ⟨hg, hr, hi, hv, _, hDual, hOrder, hiMax, hD, hz, hx, hE, _⟩
  have hm₀ : 0 ≤ q.m := hDual 0
  have hn := (q.dual_order hOrder).2.2
  obtain ⟨hDlo, hDhi⟩ := q.bounds_D hD hi hiMax hv
  have hsum : q.D = q.m + q.n + q.j := rfl
  have hb : q.sigma / 2 - q.tau ≤ q.b := by
    unfold Degrees.b
    linarith only [hm]
  have hdiff : 0 < q.b - q.j - 2 * q.r - q.tail / 5 := by
    linarith only [hb, hj, hς, hg, hr, hv, step2_b_sub_j q]
  refine ⟨by linarith only [hdiff, hr, hv], ?_, ?_, ?_, ?_⟩
  · unfold Degrees.P0
    linarith only [hdiff, hr, hz, hx, hE]
  · have hBound : 2 * q.sigma - (1 + q.ς) - 6 * q.tau -
        2 * (3 * q.g + 4 * q.r) - 4 / 5 * q.tail ≤ 4 * q.P2 := by
      unfold Degrees.P2 Degrees.a
      linarith only [hsum, hn, hDhi, hj, hiMax, hz, hx, hE]
    linarith only [hBound, step2_P2 q, hς, hg, hr, hv]
  · have hBound : q.sigma / 2 - 3 * q.tau -
        (q.r + (3 * q.g + 4 * q.r)) / 2 - q.tail / 5 ≤ q.P3 := by
      unfold Degrees.P3
      linarith only [hm₀, hj, hiMax, hz, hx, hE]
    linarith only [hBound, step2_P3 q, hς, hg, hr, hv]
  · have hBound : q.lambda - 10 * q.tau - 4 * (3 * q.g + 4 * q.r) -
        4 / 5 * q.tail + 2 * (q.Z + q.E) ≤ 4 * q.P1 := by
      unfold Degrees.P1
      linarith only [hsum, hn, hDlo, hj, hiMax]
    linarith only [hBound, step2_P1 q]

/-- Lemma 90(i), using the square margin for arbitrary values of the factor degree. -/
theorem bandI_saves (q : Degrees) (hq : q.Admissible) (hs : q.BandI) :
    q.Trivial ∨ q.Unsigned ∨ q.SpectralSquare := by
  by_cases ht : q.Trivial
  · exact Or.inl ht
  by_cases hu : q.Unsigned
  · exact Or.inr (Or.inl hu)
  have hs' : q.ς < 1 / 10 := hs
  have hs₈ : q.ς < 1 / 8 := by linarith only [hs']
  have hAdmissible : q.Admissible := hq
  rcases hq with ⟨hg, hr, hi, hv, hσ₀, hDual, hOrder, hiMax, hD, hz, hx, hE, _⟩
  have hσ := q.four_tau_lt_sigma (by linarith only [hs₈]) hg hr hv
  have hDlo := (q.bounds_D hD hi hiMax hv).1
  have hGapMax := q.D_lt_three_times_gap hs₈ hg hr hv hDlo
  have hj₀ : 0 ≤ q.dual (3 : Fin 4) := hDual 3
  obtain ⟨h43, h32, h21⟩ := q.dual_order hOrder
  have hsum : q.D = q.m + q.n + (q.dual 2 + q.dual 3) := rfl
  have hThird : q.dual 2 ≤ 2 * q.tau := by
    have hThird := q.split_gap hσ hσ₀ hu {2}
    rw [q.splitDegree_singleton 2] at hThird
    rcases hThird with h | h
    · exact h
    · linarith only [h, hsum, hGapMax, h21, h32, hj₀]
  have hGapMin : 4 * q.tau < q.D - q.splitBudget := by
    linarith only [lambda_gap_sub_four_tau q, hDlo, hg, hr, hv, hs']
  have hj : q.j ≤ 2 * q.tau := by
    rcases q.first_pair_split_failure hu hσ hσ₀ with h | h
    · exact h
    · have hjdef : q.j = q.dual 2 + q.dual 3 := rfl
      linarith only [h, hGapMin, hsum, hThird, h43, hjdef]
  obtain ⟨hPre, hP0, hP2, hP3, hP1⟩ :=
    small_j_square_bounds q hAdmissible hs₈ (q.m_le_of_not_unsigned hu) hj
  have hZ : 0 ≤ q.Z := add_nonneg hz hx
  exact Or.inr (Or.inr ⟨hPre, hP0, hP2, hP3,
    Or.inl (by linarith only [hP1, hs', hg, hr, hv, hZ, hE])⟩)

private theorem direct_of_last_three (q : Degrees) (hq : q.Admissible)
    (hτ : 0 ≤ q.tau) (hς : q.ς < 1 / 8) (hw : q.w ≤ 1 / 2) (hj : q.j ≤ 4 * q.tau)
    (hM1 : 0 < q.m - q.ς / 2 + q.g + q.r / 2 + 2 / 5 * q.tail - q.w - q.i / 2 - q.E / 2)
    (hM2 : 0 < q.m - q.ς + 2 * q.g + 2 * q.r + 4 / 5 * q.tail - q.w / 2 + q.Z + q.z)
    (hM3 : 0 < 2 * (q.m + q.n) - 2 * q.tau - 3 * q.r - q.i + q.E - q.w) :
    q.Direct := by
  rcases hq with ⟨hg, hr, hi, hv, _, hDual, hOrder, hiMax, hD, hz, hx, hE,
    _, _, hEZ, _, _, _⟩
  have hn := (q.dual_order hOrder).2.2
  have hm₀ : 0 ≤ q.m := hDual 0
  have hDlo := (q.bounds_D hD hi hiMax hv).1
  have hsum : q.D = q.m + q.n + q.j := rfl
  have hmn : 1 - 3 * q.ς ≤ q.m + q.n := by
    linarith only [lambda_sub_four_tau q, hDlo, hsum, hj, hg, hr, hv]
  have hrSmall : 3 * q.r ≤ q.ς := by
    unfold Degrees.tau at hτ
    linarith only [hτ, hg, hv]
  intro k hk
  simp only [Degrees.directTerms, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [direct_Rw_c q hD]
    linarith only [hς, hg, hr, hv, hn, hEZ, hz, hw]
  · rw [direct_Rw_Rd q hD]
    linarith only [hM1]
  · rw [direct_N_c q]
    linarith only [hς, hg, hr, hv, hm₀, hx, hz]
  · rw [direct_N_Rd q]
    linarith only [hς, hg, hr, hv, hn, hiMax, hrSmall, hmn, hx, hz, hw]
  · rwa [direct_prime_Rw q hD]
  · rw [direct_prime_N q hD]
    linarith only [hς, hg, hr, hv, hn, hmn, hx, hz, hE]
  · rwa [direct_double_prime q]

private theorem bandII_small_j (q : Degrees) (hq : q.Admissible)
    (hτ : 0 ≤ q.tau) (hς : q.ς < 1 / 8) (hw : q.w < (3 - 21 * q.ς) / 2)
    (hwHalf : q.w ≤ 1 / 2) (hm : q.m ≤ q.sigma / 2 + q.tau) (hj : q.j ≤ 2 * q.tau) :
    q.SpectralSquare ∨ q.Direct := by
  obtain ⟨hPre, hP0, hP2, hP3, hP1Bound⟩ := small_j_square_bounds q hq hς hm hj
  by_cases hP1 : 0 < q.P1
  · exact Or.inl ⟨hPre, hP0, hP2, hP3, Or.inl hP1⟩
  have hData := hq
  rcases hData with ⟨hg, hr, hi, hv, _, _, hOrder, hiMax, hD, hz, hx, hE, _⟩
  have hZ : 0 ≤ q.Z := add_nonneg hz hx
  have hn := (q.dual_order hOrder).2.2
  have hDlo := (q.bounds_D hD hi hiMax hv).1
  have hsum : q.D = q.m + q.n + q.j := rfl
  have hs₉ : 1 / 9 ≤ q.ς := by
    linarith only [hP1Bound, le_of_not_gt hP1, hg, hr, hv, hZ, hE]
  have hEmax : q.E ≤ (9 * q.ς - 1 - 5 * q.g - 10 * q.r - (36 / 5) * q.tail) / 2 := by
    linarith only [hP1Bound, le_of_not_gt hP1, hZ]
  right
  apply direct_of_last_three q hq hτ hς hwHalf (by linarith only [hj, hτ])
  · linarith only [hsum, hDlo, hn, hj, hiMax, hg, hr, hv, hEmax, hs₉, hw,
      case1_M1_first q, case1_M1_second q, case1_mark q]
  · linarith only [hsum, hDlo, hn, hj, hg, hr, hv, hZ, hz, hwHalf, hς, case1_M2 q]
  · linarith only [hsum, hDlo, hj, hiMax, hg, hr, hv, hE, hwHalf, hς, case1_M3 q]

private theorem bandII_large_j (q : Degrees) (hq : q.Admissible)
    (hτ : 0 ≤ q.tau) (hς₁ : 1 / 10 ≤ q.ς) (hς : q.ς < 1 / 8)
    (hw : q.w < (3 - 21 * q.ς) / 2) (hwHalf : q.w ≤ 1 / 2)
    (hUnsigned : ¬ q.Unsigned) (hjLarge : 2 * q.tau < q.j) : q.SpectralSquare ∨ q.Direct := by
  have hData := hq
  rcases hData with ⟨hg, hr, hi, hv, hσ₀, _, hOrder, hiMax, hD, hz, hx, hE, _, _, hEZ, _⟩
  have hZ : 0 ≤ q.Z := add_nonneg hz hx
  obtain ⟨h43, h32, h21⟩ := q.dual_order hOrder
  have hσ := q.four_tau_lt_sigma (by linarith only [hς]) hg hr hv
  have hDlo := (q.bounds_D hD hi hiMax hv).1
  have hGapMax := q.D_lt_three_times_gap hς hg hr hv hDlo
  have hsum : q.D = q.m + q.n + q.j := rfl
  have hjdef : q.j = q.dual 2 + q.dual 3 := rfl
  have hUj : q.D - q.splitBudget ≤ q.j := by
    have h := q.split_gap hσ hσ₀ hUnsigned {2, 3}
    rw [q.sum_small_eq] at h
    exact h.resolve_left (not_le_of_gt hjLarge)
  have hnSmall : q.n ≤ 2 * q.tau := by
    by_contra h
    have hnGap := q.split_gap hσ hσ₀ hUnsigned {1}
    rw [q.splitDegree_singleton 1] at hnGap
    change q.n ≤ 2 * q.tau ∨ q.D - q.splitBudget ≤ q.n at hnGap
    have hnGap := hnGap.resolve_left h
    linarith only [hUj, hGapMax, hsum, h21, hnGap]
  have hj : q.j ≤ 4 * q.tau := by linarith only [h32, h43, hnSmall, hjdef]
  have hpair := q.split_gap hσ hσ₀ hUnsigned {1, 3}
  rw [q.splitDegree_pair (by decide : (1 : Fin 4) ≠ 3)] at hpair
  change q.n + q.dual 3 ≤ 2 * q.tau ∨ _ at hpair
  have hpair := hpair.resolve_left (by linarith only [h32, hjLarge, hjdef])
  change q.D - q.splitBudget ≤ q.n + q.dual 3 at hpair
  have hnLarge : q.D - q.splitBudget - 2 * q.tau ≤ q.n := by
    linarith only [hpair, h43, h32, hnSmall]
  have hm : q.lambda - 6 * q.tau ≤ q.m := by linarith only [hsum, hDlo, hnSmall, hj]
  have hb : q.sigma / 2 - 4 * q.tau ≤ q.b - q.j := by
    unfold Degrees.b
    linarith only [hnLarge, hsum, sigma_sub_split_sub_two_tau q]
  have hdiff : 0 < q.b - q.j - 2 * q.r - q.tail / 5 := by
    linarith only [case2_b_sub_j q, hb, hς, hg, hr, hv]
  have hPre : 0 < q.b - q.j - q.r := by linarith only [hdiff, hr, hv]
  have hP0 : 0 < q.P0 := by
    unfold Degrees.P0
    linarith only [hdiff, hr, hz, hx, hE]
  have hP1Bound :
      1 - 10 * q.ς + 16 * q.g + 25 * q.r + 87 / 10 * q.tail + (q.Z + q.E) / 2 ≤ q.P1 := by
    unfold Degrees.P1
    linarith only [case2_P1 q, hm, hnSmall, hj, hiMax]
  have hP2Bound :
      1 / 2 - 5 * q.ς + 8 * q.g + 25 / 2 * q.r + 43 / 10 * q.tail +
        3 * q.z / 2 + q.x + q.E ≤ q.P2 := by
    unfold Degrees.P2 Degrees.a
    linarith only [case2_P2 q, hnSmall, hj, hiMax]
  have hP3Bound :
      1 - 17 / 2 * q.ς + 29 / 2 * q.g + 22 * q.r + 37 / 5 * q.tail +
        q.z / 2 + q.x / 2 + 3 * q.E / 2 ≤ q.P3 := by
    unfold Degrees.P3
    linarith only [case2_P3 q, hm, hj, hiMax]
  have hMargins : (0 < q.P1 ∧ 0 < q.P2 ∧ 0 < q.P3) ∨
      0 ≤ 5 * q.ς - 1 / 2 - q.E / 2 := by
    by_cases hP1 : 0 < q.P1
    · by_cases hP2 : 0 < q.P2
      · by_cases hP3 : 0 < q.P3
        · exact Or.inl ⟨hP1, hP2, hP3⟩
        · have hEmax : q.E ≤ (17 * q.ς - 2) / 3 := by
            linarith only [hP3Bound, le_of_not_gt hP3, hg, hr, hv, hz, hx]
          exact Or.inr (by linarith only [hEmax, hς₁])
      · have hEmax : q.E ≤ 5 * q.ς - 1 / 2 := by
          linarith only [hP2Bound, le_of_not_gt hP2, hg, hr, hv, hz, hx]
        exact Or.inr (by linarith only [hEmax, hς₁])
    · have hEmax : q.E ≤ 10 * q.ς - 1 := by
        linarith only [hP1Bound, le_of_not_gt hP1, hg, hr, hv, hEZ]
      exact Or.inr (by linarith only [hEmax])
  rcases hMargins with ⟨hP1, hP2, hP3⟩ | hM1
  · exact Or.inl ⟨hPre, hP0, hP2, hP3, Or.inl hP1⟩
  right
  apply direct_of_last_three q hq hτ hς hwHalf hj
  · linarith only [case2_M1 q, case2_mark q, hm, hiMax, hw, hg, hr, hv, hM1]
  · linarith only [case2_M2 q, hm, hwHalf, hg, hr, hv, hZ, hz, hς]
  · linarith only [case2_M3 q, hD, hsum, hj, hi, hE, hwHalf, hg, hr, hv, hς]

/-- Lemma 90(ii), with both the small and large complementary degree cases. -/
theorem bandII_saves (q : Degrees) (hq : q.Admissible) (hs : q.BandII) :
    q.Trivial ∨ q.Unsigned ∨ q.SpectralSquare ∨ q.Direct := by
  by_cases ht : q.Trivial
  · exact Or.inl ht
  by_cases hu : q.Unsigned
  · exact Or.inr (Or.inl hu)
  obtain ⟨hs₁, hs₂, hmark⟩ := hs
  have hwMark : q.w ≤ q.mark := by
    rcases hq with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hle⟩
    exact hle
  have hw : q.w < (3 - 21 * q.ς) / 2 := lt_of_le_of_lt hwMark hmark
  have hwHalf : q.w ≤ 1 / 2 := by linarith only [hw, hs₁]
  have hτ := q.tau_nonneg_of_not_trivial ht
  right
  right
  by_cases hj : q.j ≤ 2 * q.tau
  · exact bandII_small_j q hq hτ hs₂ hw hwHalf (q.m_le_of_not_unsigned hu) hj
  · exact bandII_large_j q hq hτ hs₁ hs₂ hw hwHalf hu (lt_of_not_ge hj)

end ZetaSixth.Exponents

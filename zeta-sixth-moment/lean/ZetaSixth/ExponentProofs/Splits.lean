import ZetaSixth.ExponentProofs.Identities

namespace ZetaSixth.Exponents

open scoped BigOperators

namespace Degrees

variable (q : Degrees)

theorem tau_nonneg_of_not_trivial (h : ¬ q.Trivial) : 0 ≤ q.tau :=
  neg_nonpos.mp <| le_of_not_gt fun hτ => h (Or.inl hτ)

theorem u_nonneg_of_not_trivial (h : ¬ q.Trivial) : 0 ≤ q.u :=
  neg_nonpos.mp <| le_of_not_gt fun hu => h (Or.inr hu)

theorem m_le_of_not_unsigned (h : ¬ q.Unsigned) : q.m ≤ q.sigma / 2 + q.tau := by
  apply le_of_not_gt
  intro hm
  exact h (Or.inl (by linarith only [hm]))

theorem splitDegree_singleton (k : Fin 4) : q.splitDegree {k} = q.dual k := by
  simp [splitDegree]

theorem splitDegree_pair {a b : Fin 4} (hab : a ≠ b) :
    q.splitDegree {a, b} = q.dual a + q.dual b := by
  unfold splitDegree
  rw [Finset.sum_insert (by simpa using hab), Finset.sum_singleton]

theorem splitDegree_compl_add (s : Finset (Fin 4)) :
    q.splitDegree s + q.splitDegree sᶜ = q.D := by
  have h := Finset.sum_union (f := q.dual) (disjoint_compl_right : Disjoint s sᶜ)
  rw [Finset.union_compl, show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide] at h
  rw [Finset.sum_insert (by decide : (0 : Fin 4) ∉ ({1, 2, 3} : Finset (Fin 4))),
    Finset.sum_insert (by decide : (1 : Fin 4) ∉ ({2, 3} : Finset (Fin 4))),
    Finset.sum_insert (by decide : (2 : Fin 4) ∉ ({3} : Finset (Fin 4))), Finset.sum_singleton] at h
  unfold splitDegree D m n j
  linarith only [h]

theorem splitBudget_ge (hSigma : 0 ≤ q.sigma) : 2 * q.tau ≤ q.splitBudget := by
  unfold splitBudget
  linarith only [hSigma]

/-- A split with both degrees above the smaller cutoff and at least one above the
larger cutoff proves the split alternative of Lemma 84. -/
theorem unsigned_of_split {s : Finset (Fin 4)} (hσ : 4 * q.tau < q.sigma)
    (hs : 2 * q.tau < q.splitDegree s) (hc : 2 * q.tau < q.splitDegree sᶜ)
    (hLarge : q.splitBudget < q.splitDegree s ∨ q.splitBudget < q.splitDegree sᶜ) :
    q.Unsigned := by
  apply Or.inr
  refine ⟨by linarith only [hσ], ?_⟩
  rcases le_total (q.splitDegree s) (q.splitDegree sᶜ) with h | h
  · refine ⟨s, h, by linarith only [hs], ?_⟩
    rcases hLarge with hLarge | hLarge
    · linarith only [h, hLarge]
    · linarith only [hLarge]
  · refine ⟨sᶜ, ?_⟩
    rw [compl_compl]
    refine ⟨h, by linarith only [hc], ?_⟩
    rcases hLarge with hLarge | hLarge
    · linarith only [hLarge]
    · linarith only [h, hLarge]

/-- Step 1 of Lemma 90. If the split bound fails, each subset of the dual variables
lies on one side of the gap between the two degree thresholds. -/
theorem split_gap (hσ : 4 * q.tau < q.sigma) (hσ₀ : 0 ≤ q.sigma)
    (hUnsigned : ¬ q.Unsigned) (s : Finset (Fin 4)) :
    q.splitDegree s ≤ 2 * q.tau ∨ q.D - q.splitBudget ≤ q.splitDegree s := by
  by_cases hSmall : q.splitDegree s ≤ 2 * q.tau
  · exact Or.inl hSmall
  · right
    apply le_of_not_gt
    intro hLarge
    have h := q.splitDegree_compl_add s
    have hc : q.splitBudget < q.splitDegree sᶜ := by linarith only [h, hLarge]
    exact hUnsigned (q.unsigned_of_split hσ (lt_of_not_ge hSmall)
      (lt_of_le_of_lt (q.splitBudget_ge hσ₀) hc) (Or.inr hc))

theorem dual_order (h : Antitone q.dual) :
    q.dual 3 ≤ q.dual 2 ∧ q.dual 2 ≤ q.n ∧ q.n ≤ q.m :=
  ⟨h (show (2 : Fin 4) ≤ 3 by decide), h (show (1 : Fin 4) ≤ 2 by decide),
    h (show (0 : Fin 4) ≤ 1 by decide)⟩

theorem sum_small_eq (q : Degrees) : q.splitDegree {2, 3} = q.j :=
  q.splitDegree_pair (by decide)

theorem bounds_D (hD : q.D = q.lambda + q.i) (hi : 0 ≤ q.i)
    (hiMax : q.i ≤ 3 * q.g + 4 * q.r) (htail : 0 ≤ q.tail) :
    q.lambda ≤ q.D ∧ q.D ≤ 1 + q.ς := by
  constructor
  · linarith only [hD, hi]
  · unfold lambda at hD
    linarith only [hD, hiMax, htail]

theorem four_tau_lt_sigma (hς : q.ς < 1 / 4) (hg : 0 ≤ q.g) (hr : 0 ≤ q.r)
    (htail : 0 ≤ q.tail) : 4 * q.tau < q.sigma := by
  linarith only [hς, hg, hr, htail, Identities.sigma_sub_four_tau q]

theorem D_lt_three_times_gap (hς : q.ς < 1 / 8) (hg : 0 ≤ q.g) (hr : 0 ≤ q.r)
    (htail : 0 ≤ q.tail) (hD : q.lambda ≤ q.D) :
    q.D < 3 * (q.D - q.splitBudget) := by
  linarith only [hς, hg, hr, htail, hD, Identities.two_thirds_lambda_sub_split q]

theorem first_pair_split_failure (hUnsigned : ¬ q.Unsigned) (hσ : 4 * q.tau < q.sigma)
    (hσ₀ : 0 ≤ q.sigma) :
    q.j ≤ 2 * q.tau ∨ q.m + q.n ≤ q.splitBudget := by
  have hp := q.split_gap hσ hσ₀ hUnsigned {2, 3}
  rw [q.sum_small_eq] at hp
  rcases hp with h | h
  · exact Or.inl h
  · unfold D at h
    exact Or.inr (by linarith only [h])

theorem singleton_split_failure (hUnsigned : ¬ q.Unsigned) (hσ : 4 * q.tau < q.sigma) :
    q.m ≤ 2 * q.tau ∨ q.D - q.m ≤ 2 * q.tau ∨ q.D - q.m ≤ q.splitBudget := by
  let s : Finset (Fin 4) := {0}
  have hs : q.splitDegree s = q.m := q.splitDegree_singleton 0
  have hc : q.splitDegree sᶜ = q.D - q.m := by
    linarith only [q.splitDegree_compl_add s, hs]
  by_cases hm : q.m ≤ 2 * q.tau
  · exact Or.inl hm
  by_cases hD : q.D - q.m ≤ 2 * q.tau
  · exact Or.inr (Or.inl hD)
  by_cases hB : q.D - q.m ≤ q.splitBudget
  · exact Or.inr (Or.inr hB)
  exfalso
  apply hUnsigned
  exact q.unsigned_of_split hσ (by rw [hs]; exact lt_of_not_ge hm)
    (by rw [hc]; exact lt_of_not_ge hD) (Or.inr (by rw [hc]; exact lt_of_not_ge hB))

end Degrees

end ZetaSixth.Exponents

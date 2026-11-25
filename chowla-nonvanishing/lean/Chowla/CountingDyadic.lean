import Chowla.CountingShells
import Mathlib.Data.Finset.CastCard
import Mathlib.Data.Int.Interval

namespace Chowla

open Filter
open scoped BigOperators Topology

/-- The weighted limiting bound implies the corresponding sharp shell bound.
The mass limits here are the two conclusions of the elementary squarefree count. -/
theorem eventual_sharpShell_rate_of_limits (D : DiscClass) {p q : ℝ} (hq : 0 < q) (hp : q < p)
    (hMass : ∀ W : ShellWeight,
      Tendsto (fun X => weightedSum D W X (fun _ => 1) / X) atTop
        (𝓝 (classDensity D * ∫ u : ℝ, W.toFun u)))
    (hShell : Tendsto (fun X => ((sharpShell D X).card : ℝ) / X) atTop (𝓝 (classDensity D)))
    (hweighted : ∀ W : ShellWeight, ∀ ε > 0, ∀ᶠ X in atTop,
      p - ε ≤ weightedAverage D W X nonvanishingIndicator) :
    ∀ᶠ X in atTop,
      q * ((sharpShell D X).card : ℝ) ≤ ((nonvanishing (sharpShell D X)).card : ℝ) := by
  let ε := (p - q) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let r := p - ε
  have hqr : q < r := by dsimp [r, ε]; linarith
  have hr : 0 < r := hq.trans hqr
  let e := min (1 / 2 : ℝ) ((r - q) / (2 * r))
  have he : 0 < e := lt_min (by norm_num) (div_pos (sub_pos.mpr hqr) (by positivity))
  have he' : e < 1 := (min_le_left _ _).trans_lt (by norm_num)
  obtain ⟨W, hW, hI⟩ := exists_shellWeight_large_integral e he he'
  have hcost : e * (2 * r) ≤ r - q :=
    (le_div_iff₀ (by positivity : 0 < 2 * r)).mp (min_le_right _ _)
  have hrate : q < r * ∫ u : ℝ, W.toFun u := by
    have haux : q < r * (1 - e) := by nlinarith only [hcost, hqr]
    exact haux.trans_le (mul_le_mul_of_nonneg_left hI hr.le)
  have hc := classDensity_pos D
  have hpos : 0 < r * (classDensity D * ∫ u : ℝ, W.toFun u) - q * classDensity D := by
    nlinarith only [mul_lt_mul_of_pos_right hrate hc]
  have hlim := ((hMass W).const_mul r).sub (hShell.const_mul q)
  have hcomp : ∀ᶠ X in atTop,
      0 < r * (weightedSum D W X (fun _ => 1) / X) - q * (((sharpShell D X).card : ℝ) / X) :=
    hlim.eventually (Ioi_mem_nhds hpos)
  filter_upwards [hweighted W ε hε, eventually_weightedMass_pos_of_limit D W (hMass W),
    hcomp, eventually_gt_atTop (0 : ℝ)] with X hbound hmass hcx hX
  have hsharp : q * ((sharpShell D X).card : ℝ) < r * weightedSum D W X (fun _ => 1) := by
    rw [← mul_div_assoc, ← mul_div_assoc, ← sub_div, div_pos_iff] at hcx
    exact sub_pos.mp (hcx.resolve_right (fun h => hX.not_gt h.2)).1
  have hWbound : r * weightedSum D W X (fun _ => 1) ≤ weightedSum D W X nonvanishingIndicator :=
    (le_div_iff₀ hmass).mp hbound
  exact hsharp.le.trans (hWbound.trans (weighted_nonvanishing_le_sharpShell D W hX hW))

theorem mem_discs_iff_abs {X : ℝ} {d : ℤ} :
    d ∈ discs X ↔ ((|d| : ℤ) : ℝ) ≤ X ∧ IsFundDisc d ∧ 1 < |d| := by
  rw [mem_discs_iff, ← and_assoc, ← abs_le, Int.le_floor]

theorem classDiscs_mono (D : DiscClass) : Monotone (classDiscs D) := by
  intro a b hab d hd
  obtain ⟨hd, hD⟩ := mem_classDiscs_iff.mp hd
  obtain ⟨hcut, hd, hlt⟩ := mem_discs_iff_abs.mp hd
  exact mem_classDiscs_iff.mpr ⟨mem_discs_iff_abs.mpr ⟨hcut.trans hab, hd, hlt⟩, hD⟩

theorem kappa_pos (D : DiscClass) : 0 < (D.2.kappa : ℝ) := by cases D.2 <;> norm_num [DiscType.kappa]

theorem sharpShell_eq_sdiff (D : DiscClass) (Y : ℝ) :
    sharpShell D Y = classDiscs D (2 * (D.2.kappa : ℝ) * Y) \
      classDiscs D ((D.2.kappa : ℝ) * Y) := by
  classical
  ext d
  simp only [sharpShell, Finset.mem_filter, Finset.mem_sdiff]
  refine and_congr_right fun hd => ?_
  have heq : Y < oddPart D d ↔ ((D.2.kappa : ℝ) * Y) < ((|d| : ℤ) : ℝ) := by
    unfold oddPart
    rw [lt_div_iff₀ (kappa_pos D), Int.abs_eq_natAbs, Int.cast_natCast, mul_comm Y]
  rw [heq]
  obtain ⟨hd, hD⟩ := mem_classDiscs_iff.mp hd
  obtain ⟨_, hd, hlt⟩ := mem_discs_iff_abs.mp hd
  simp [mem_classDiscs_iff, mem_discs_iff_abs, hd, hlt, hD]

section Dyadic

variable (D : DiscClass)

private theorem classDiscs_card_le (Y : ℝ) (hY : 0 ≤ Y) : ((classDiscs D Y).card : ℝ) ≤ 2 * Y + 1 := by
  have hsub : classDiscs D Y ⊆ Finset.Icc (-⌊Y⌋) ⌊Y⌋ := by
    intro d hd
    have h := mem_discs_iff.mp ((mem_classDiscs_iff.mp hd).1)
    exact Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩
  have hcard := Finset.card_mono hsub
  have hf : 0 ≤ ⌊Y⌋ := Int.floor_nonneg.mpr hY
  have heq : (((Finset.Icc (-⌊Y⌋) ⌊Y⌋ : Finset ℤ).card : ℕ) : ℤ) = ⌊Y⌋ + 1 - -⌊Y⌋ :=
    Int.card_Icc_of_le (-⌊Y⌋) ⌊Y⌋ (by omega)
  have heqR : ((Finset.Icc (-⌊Y⌋) ⌊Y⌋ : Finset ℤ).card : ℝ) =
      (⌊Y⌋ : ℝ) + 1 - -(⌊Y⌋ : ℝ) := by exact_mod_cast heq
  have hle : ((classDiscs D Y).card : ℝ) ≤ ((Finset.Icc (-⌊Y⌋) ⌊Y⌋ : Finset ℤ).card : ℝ) := by
    exact_mod_cast hcard
  linarith only [hle, heqR, Int.floor_le Y]

private theorem rate_of_dyadicShells {X r : ℝ} (hX : 0 ≤ X) (J : ℕ)
    (h : ∀ j < J,
      r * ((classDiscs D (X / 2^j) \ classDiscs D (X / 2^(j + 1))).card : ℝ) ≤
        ((nonvanishing
          (classDiscs D (X / 2^j) \ classDiscs D (X / 2^(j + 1)))).card : ℝ)) :
    r * (((classDiscs D X).card : ℝ) - ((classDiscs D (X / 2^J)).card : ℝ)) ≤
      ((nonvanishing (classDiscs D X)).card : ℝ) := by
  classical
  have hmono (j : ℕ) : classDiscs D (X / 2^(j + 1)) ⊆ classDiscs D (X / 2^j) := by
    apply classDiscs_mono D
    apply div_le_div_of_nonneg_left hX (by positivity)
    rw [pow_succ]
    exact le_mul_of_one_le_right (by positivity) (by norm_num)
  have hnv (j : ℕ) :
      nonvanishing (classDiscs D (X / 2^j) \ classDiscs D (X / 2^(j + 1))) =
        nonvanishing (classDiscs D (X / 2^j)) \ nonvanishing (classDiscs D (X / 2^(j + 1))) := by
    ext d
    simp [nonvanishing]
    tauto
  have hstep (j : ℕ) (hj : j < J) :
      r * (((classDiscs D (X / 2^j)).card : ℝ) - ((classDiscs D (X / 2^(j+1))).card : ℝ)) ≤
      ((nonvanishing (classDiscs D (X / 2^j))).card : ℝ) -
        ((nonvanishing (classDiscs D (X / 2^(j+1)))).card : ℝ) := by
    have hj' := h j hj
    rw [hnv j, Finset.cast_card_sdiff (hmono j), Finset.cast_card_sdiff] at hj'
    · exact hj'
    · exact Finset.filter_subset_filter _ (hmono j)
  have H (n : ℕ) (hn : n ≤ J) :
      r * (((classDiscs D X).card : ℝ) - ((classDiscs D (X / 2^n)).card : ℝ)) ≤
      ((nonvanishing (classDiscs D X)).card : ℝ) -
        ((nonvanishing (classDiscs D (X / 2^n))).card : ℝ) := by
    induction n with
    | zero => simp
    | succ j ih =>
        have hprev := ih (by omega)
        have hnext := hstep j (by omega)
        linarith only [hprev, hnext]
  exact (H J le_rfl).trans (sub_le_self _ (by positivity))

private theorem classDiscs_linear_lower_of_limit
    (hShell : Tendsto (fun X => ((sharpShell D X).card : ℝ) / X) atTop (𝓝 (classDensity D))) :
    ∀ᶠ X in atTop,
      classDensity D / (4 * ↑D.2.kappa) * X ≤ ((classDiscs D X).card : ℝ) := by
  let κ : ℝ := D.2.kappa
  have hκ : 0 < κ := kappa_pos D
  have hhalf : classDensity D / 2 < classDensity D := half_lt_self (classDensity_pos D)
  have hlarge : ∀ᶠ Y in atTop, classDensity D / 2 < ((sharpShell D Y).card : ℝ) / Y :=
    hShell.eventually (Ioi_mem_nhds hhalf)
  have hscale : Tendsto (fun X : ℝ => X / (2 * κ)) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (by positivity)).2 tendsto_id
  filter_upwards [hscale.eventually hlarge, eventually_gt_atTop (0 : ℝ)] with X hX hpos
  have hY : 0 < X / (2 * κ) := by positivity
  have hs : classDensity D / 2 * (X / (2 * κ)) < ((sharpShell D (X / (2 * κ))).card : ℝ) :=
    (lt_div_iff₀ hY).mp hX
  have hcut : 2 * (D.2.kappa : ℝ) * (X / (2 * κ)) = X := by
    change 2 * κ * (X / (2 * κ)) = X
    field_simp
  have hsub : sharpShell D (X / (2 * κ)) ⊆ classDiscs D X := by
    unfold sharpShell
    rw [hcut]
    exact Finset.filter_subset _ _
  calc
    _ = classDensity D / 2 * (X / (2 * κ)) := by ring
    _ ≤ ((sharpShell D (X / (2 * κ))).card : ℝ) := hs.le
    _ ≤ _ := by exact_mod_cast Finset.card_mono hsub

/-- Dyadic decomposition of a large discriminant cutoff, with a vanishing relative tail.
The two count limits in the hypotheses are exactly the squarefree shell mass formula. -/
theorem sharp_count_of_weighted_of_limits (p q : ℝ) (hq : q < p)
    (hMass : ∀ W : ShellWeight,
      Tendsto (fun X => weightedSum D W X (fun _ => 1) / X) atTop
        (𝓝 (classDensity D * ∫ u : ℝ, W.toFun u)))
    (hShell : Tendsto (fun X => ((sharpShell D X).card : ℝ) / X) atTop (𝓝 (classDensity D)))
    (hweighted : ∀ W : ShellWeight, ∀ ε > 0, ∀ᶠ X in atTop,
      p - ε ≤ weightedAverage D W X nonvanishingIndicator) :
    ∀ᶠ X in atTop, q * ((classDiscs D X).card : ℝ) ≤
      ((nonvanishing (classDiscs D X)).card : ℝ) := by
  by_cases hqpos : 0 < q
  · let r := (q + p) / 2
    have hqr : q < r := by dsimp [r]; linarith
    have hrp : r < p := by dsimp [r]; linarith
    have hr := hqpos.trans hqr
    have hRate := eventual_sharpShell_rate_of_limits D hr hrp hMass hShell hweighted
    let κ : ℝ := D.2.kappa
    have hκ : 0 < κ := kappa_pos D
    let β := classDensity D / (4 * κ)
    have hβ : 0 < β := div_pos (classDensity_pos D) (by positivity)
    let τ := (r - q) * β / (2 * r)
    have hτ : 0 < τ := div_pos (mul_pos (sub_pos.mpr hqr) hβ) (by positivity)
    have hPow : Tendsto (fun J : ℕ => (2 : ℝ)^J) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    obtain ⟨J, hJ⟩ := (hPow.eventually_gt_atTop (2 / τ)).exists
    have hJP : 0 < (2 : ℝ)^J := by positivity
    have hJtail : 2 / (2 : ℝ)^J < τ := by
      apply (div_lt_iff₀ hJP).mpr
      simpa only [mul_comm] using (div_lt_iff₀ hτ).mp hJ
    have hSmall : ∀ᶠ X : ℝ in atTop, X⁻¹ < τ :=
      tendsto_inv_atTop_zero.eventually (Iio_mem_nhds hτ)
    have hEach (j : ℕ) : ∀ᶠ X in atTop,
        r * ((classDiscs D (X / 2^j) \ classDiscs D (X / 2^(j+1))).card : ℝ) ≤
        ((nonvanishing (classDiscs D (X / 2^j) \ classDiscs D (X / 2^(j+1)))).card : ℝ) := by
      have hP : 0 < (2 : ℝ)^j := by positivity
      let a := (2 : ℝ)^(j+1) * κ
      have ha : 0 < a := by dsimp [a]; positivity
      have haTop : Tendsto (fun X : ℝ => X / a) atTop atTop :=
        (tendsto_div_const_atTop_of_pos ha).2 tendsto_id
      filter_upwards [haTop.eventually hRate] with X hX
      have h₀ : κ * (X / a) = X / 2^(j+1) := by
        dsimp only [a]
        field_simp
      have h₁ : 2 * κ * (X / a) = X / 2^j := by
        rw [mul_assoc, h₀, pow_succ]
        field_simp
      change r * ((sharpShell D (X / a)).card : ℝ) ≤
        ((nonvanishing (sharpShell D (X / a))).card : ℝ) at hX
      rw [sharpShell_eq_sdiff] at hX
      change r * ((classDiscs D (2 * κ * (X / a)) \ classDiscs D (κ * (X / a))).card : ℝ) ≤
        ((nonvanishing (classDiscs D (2 * κ * (X / a)) \ classDiscs D (κ * (X / a)))).card : ℝ) at hX
      rwa [h₀, h₁] at hX
    have hAll := (Finset.range J).eventually_all.2 (fun j _ => hEach j)
    filter_upwards [hAll, hSmall, eventually_gt_atTop (0 : ℝ), classDiscs_linear_lower_of_limit D hShell]
      with X hXall hXsmall hXpos hXmass
    have hsum := rate_of_dyadicShells D hXpos.le J (fun j hj => hXall j (Finset.mem_range.mpr hj))
    have htail := classDiscs_card_le D (X / 2^J) (by positivity)
    have hA : 2 * (X / 2^J) < τ * X := by
      convert mul_lt_mul_of_pos_right hJtail hXpos using 1
      ring
    have hB : 1 < τ * X := (div_lt_iff₀ hXpos).mp (by simpa [one_div] using hXsmall)
    have hC : r * (2 * (τ * X)) = (r - q) * β * X := by
      unfold τ
      field_simp
    have htailRate : r * ((classDiscs D (X / 2^J)).card : ℝ) ≤
        (r - q) * ((classDiscs D X).card : ℝ) := by
      calc
        _ ≤ r * (2 * (X / 2^J) + 1) := mul_le_mul_of_nonneg_left htail hr.le
        _ ≤ r * (2 * (τ * X)) := mul_le_mul_of_nonneg_left (by linarith only [hA, hB]) hr.le
        _ = (r - q) * (β * X) := by rw [hC]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hXmass (sub_nonneg.mpr hqr.le)
    linarith only [hsum, htailRate]
  · exact Eventually.of_forall fun X =>
      (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hqpos) (by positivity)).trans (by positivity)

end Dyadic

end Chowla

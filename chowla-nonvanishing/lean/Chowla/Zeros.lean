import Chowla.Claims
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Chowla

open Filter
open scoped BigOperators Topology

private theorem natAbs_gt_one {d : ℤ} (hd : 1 < |d|) : 1 < d.natAbs := by
  rw [Int.abs_eq_natAbs] at hd
  exact_mod_cast hd

private theorem quadraticL_analyticOnNhd (d : ℤ) [NeZero d.natAbs] :
    AnalyticOnNhd ℂ (quadraticL d) ({1}ᶜ : Set ℂ) := by
  have heq : quadraticL d = DirichletCharacter.LFunction (chi d) :=
    funext (quadraticL_eq d)
  rw [heq]
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro s hs
  exact (DirichletCharacter.differentiableAt_LFunction (chi d) s
    (.inl (by simpa using hs))).differentiableWithinAt

/-- The L-function has finite analytic order at every point away from its possible pole. -/
theorem quadraticL_order_ne_top (d : ℤ) [NeZero d.natAbs] (s : ℂ) (hs : s ≠ 1) :
    analyticOrderAt (quadraticL d) s ≠ ⊤ := by
  have hconnected : IsConnected ({1}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) 1
  have hre : 1 < (2 : ℂ).re := by norm_num
  have hvalue : quadraticL d 2 ≠ 0 := by
    rw [quadraticL_eq, DirichletCharacter.LFunction_eq_LSeries _ hre]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re _ hre
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected (quadraticL_analyticOnNhd d)
    hconnected.isPreconnected (x := 2) (by simp) (by simpa using hs) (by
      rw [analyticOrderAt_eq_zero.mpr (.inr hvalue)]
      simp)

private theorem analyticAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Complex.Gammaℝ s := by
  have h := (Complex.differentiable_Gammaℝ_inv.analyticAt s).inv
    (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hs))
  simpa only [Pi.inv_def, inv_inv] using h

private theorem gammaFactor_at_half (d : ℤ) [NeZero d.natAbs] :
    AnalyticAt ℂ (DirichletCharacter.gammaFactor (chi d)) (1 / 2) ∧
      DirichletCharacter.gammaFactor (chi d) (1 / 2) ≠ 0 := by
  by_cases heven : (chi d).Even
  · have heq : DirichletCharacter.gammaFactor (chi d) = Complex.Gammaℝ :=
      funext heven.gammaFactor_def
    rw [heq]
    have hre : 0 < (1 / 2 : ℂ).re := by norm_num [Complex.div_re]
    exact ⟨analyticAt_Gammaℝ_of_re_pos hre, Complex.Gammaℝ_ne_zero_of_re_pos hre⟩
  · have heq : DirichletCharacter.gammaFactor (chi d) = fun s => Complex.Gammaℝ (s + 1) := by
      funext s
      simp [DirichletCharacter.gammaFactor, heven]
    rw [heq]
    have hre : 0 < (1 / 2 + 1 : ℂ).re := by norm_num [Complex.div_re]
    have h := analyticAt_Gammaℝ_of_re_pos hre
    refine ⟨?_, Complex.Gammaℝ_ne_zero_of_re_pos hre⟩
    exact h.comp' (f := fun z : ℂ => z + 1) (x := (1 / 2 : ℂ)) (by fun_prop)

private theorem completed_at_half (d : ℤ) (hd : 1 < |d|) :
    AnalyticAt ℂ (completed d) (1 / 2) ∧
      analyticOrderAt (completed d) (1 / 2) = analyticOrderAt (quadraticL d) (1 / 2) := by
  have hN := natAbs_gt_one hd
  have hN₀ : d.natAbs ≠ 0 := by omega
  have hN₁ : d.natAbs ≠ 1 := by omega
  letI : NeZero d.natAbs := ⟨hN₀⟩
  let center : ℂ := 1 / 2
  let scale := fun s : ℂ => (d.natAbs : ℂ) ^ (s / 2)
  have hConductor : (d.natAbs : ℂ) ≠ 0 := by exact_mod_cast hN₀
  have hscale : AnalyticAt ℂ scale center := by
    change AnalyticAt ℂ (fun s : ℂ => (d.natAbs : ℂ) ^ (s / 2)) center
    simp_rw [Complex.cpow_def_of_ne_zero hConductor]
    fun_prop
  have hscale₀ : scale center ≠ 0 := by
    change (d.natAbs : ℂ) ^ (center / 2) ≠ 0
    rw [Complex.cpow_def_of_ne_zero hConductor]
    exact Complex.exp_ne_zero _
  obtain ⟨hgamma, hgamma₀⟩ := gammaFactor_at_half d
  have hL : AnalyticAt ℂ (quadraticL d) center :=
    quadraticL_analyticOnNhd d _ (by norm_num [center])
  have heq : completed d =ᶠ[𝓝 center]
      fun s => scale s * (quadraticL d s * DirichletCharacter.gammaFactor (chi d) s) := by
    have hgEventually : ∀ᶠ s in 𝓝 center, DirichletCharacter.gammaFactor (chi d) s ≠ 0 :=
      hgamma.continuousAt.eventually_ne hgamma₀
    filter_upwards [hgEventually] with s hs
    rw [quadraticL_eq, DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ _ (.inr hN₁),
      div_mul_cancel₀ _ hs]
    simp only [completed, dif_neg hN₀, scale]
  constructor
  · exact (hscale.mul (hL.mul hgamma)).congr heq.symm
  · rw [analyticOrderAt_congr heq]
    change analyticOrderAt (scale * (quadraticL d * DirichletCharacter.gammaFactor (chi d))) center =
      analyticOrderAt (quadraticL d) center
    rw [analyticOrderAt_mul hscale (hL.mul hgamma), analyticOrderAt_mul hL hgamma,
      hscale.analyticOrderAt_eq_zero.mpr hscale₀, hgamma.analyticOrderAt_eq_zero.mpr hgamma₀,
      zero_add, add_zero]

private theorem even_order_of_reflection {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (hfinite : analyticOrderAt f a ≠ ⊤) (hmid : 1 - a = a)
    (hreflect : ∀ s, f s = f (1 - s)) :
    Even (analyticOrderNatAt f a) := by
  let n := analyticOrderNatAt f a
  have hn : (n : ℕ∞) = analyticOrderAt f a := Nat.cast_analyticOrderNatAt hfinite
  refine (Nat.even_or_odd n).resolve_right ?_
  intro hodd
  have hreflect' : f = fun s => f (1 - s) := funext hreflect
  have hval : iteratedDeriv n f a = -iteratedDeriv n f a := by
    calc
      iteratedDeriv n f a = iteratedDeriv n (fun s => f (1 - s)) a :=
        congrArg (fun g => iteratedDeriv n g a) hreflect'
      _ = -iteratedDeriv n f a := by
        rw [iteratedDeriv_comp_const_sub]
        simp only [hmid, hodd.neg_one_pow, neg_one_smul]
  have hzero : iteratedDeriv n f a = 0 := by
    let v := iteratedDeriv n f a
    have htwo : (2 : ℂ) * v = 0 := calc
      2 * v = v + v := two_mul v
      _ = v + -v := congrArg (v + ·) hval
      _ = 0 := add_neg_cancel v
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hvanish := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mp hn.le
  have hle : (↑(n + 1) : ℕ∞) ≤ analyticOrderAt f a := by
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mpr
    intro i hi
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
    · exact hvanish i hlt
    · exact hzero
  rw [← hn] at hle
  exact (Nat.not_succ_le_self n) (ENat.coe_le_coe.mp hle)

/-- Lemma 4. The central zero has even multiplicity. -/
theorem even_central_order (c : CitedFacts) (d : ℤ) (hd : IsFundDisc d) (hd' : 1 < |d|) :
    ∃ k : ℕ, analyticOrderAt (quadraticL d) (1 / 2) = ((2 * k : ℕ) : ℕ∞) := by
  obtain ⟨hcompleted, horder⟩ := completed_at_half d hd'
  letI : NeZero d.natAbs := ⟨by have := natAbs_gt_one hd'; omega⟩
  have hfinite : analyticOrderAt (completed d) (1 / 2) ≠ ⊤ := by
    rw [horder]
    exact quadraticL_order_ne_top d _ (by norm_num)
  obtain ⟨k, hk⟩ :=
    even_order_of_reflection hcompleted hfinite (by norm_num) (c.rootNumberOne d hd hd')
  refine ⟨k, ?_⟩
  rw [← horder, ← Nat.cast_analyticOrderNatAt hfinite, hk, two_mul]

private def halfOpenZeroBand (d : ℤ) (n : ℕ) : Set (ZeroCopy d) :=
  {z | (n : ℝ) ≤ |z.ordinate| ∧ |z.ordinate| < (n : ℝ) + 1}

private theorem halfOpenZeroBand_subset (d : ℤ) (n : ℕ) :
    halfOpenZeroBand d n ⊆ zerosInBand d n :=
  fun _ h => ⟨h.1, h.2.le⟩

private theorem halfOpenZeroBand_partition (d : ℤ) (z : ZeroCopy d) :
    ∃! n : ℕ, z ∈ halfOpenZeroBand d n := by
  refine ⟨⌊|z.ordinate|⌋₊, ⟨Nat.floor_le (abs_nonneg _), Nat.lt_floor_add_one _⟩,
    fun n hn => ?_⟩
  exact ((Nat.floor_eq_iff (abs_nonneg _)).mpr hn).symm

private theorem decay_bound {C q t a : ℝ} (hC : 0 ≤ C) (hq : 0 < q)
    (ha : 0 ≤ a) (hat : a ≤ |t|) :
    C / (1 + (t * q)^2) ≤ (2 * C / min 1 (q^2)) / (a + 1)^2 := by
  let k := min 1 (q^2)
  have hk : 0 < k := lt_min (by norm_num) (sq_pos_of_pos hq)
  have hkt : k * (1 + t^2) ≤ 1 + (t * q)^2 := by
    have hk₁ : k ≤ 1 := min_le_left _ _
    have hk₂ : k ≤ q^2 := min_le_right _ _
    nlinarith [mul_le_mul_of_nonneg_right hk₂ (sq_nonneg t)]
  have ha₂ : a^2 ≤ t^2 := by
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg ha] using hat)
  have hab : (a + 1)^2 ≤ 2 * (1 + t^2) := by
    nlinarith [sq_nonneg (a - 1)]
  have hbl : k * (a + 1)^2 ≤ 2 * (1 + (t * q)^2) := by
    calc
      k * (a + 1)^2 ≤ k * (2 * (1 + t^2)) := mul_le_mul_of_nonneg_left hab hk.le
      _ = 2 * (k * (1 + t^2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hkt (by norm_num)
  change C / (1 + (t * q)^2) ≤ (2 * C / k) / (a + 1)^2
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  calc
    C * (a + 1)^2 = (C / k) * (k * (a + 1)^2) := by
      rw [← mul_assoc, div_mul_cancel₀ _ hk.ne']
    _ ≤ (C / k) * (2 * (1 + (t * q)^2)) := mul_le_mul_of_nonneg_left hbl (by positivity)
    _ = (2 * C / k) * (1 + (t * q)^2) := by ring

private theorem log_growth_bound {N : ℝ} (hN : 0 ≤ N) (a : ℝ) (ha : 0 ≤ a) :
    Real.log (N * (a + 2)) ≤ 2 * (2 * N) ^ (1/2 : ℝ) * (a + 1) ^ (1/2 : ℝ) := by
  have h : N * (a + 2) ≤ (2 * N) * (a + 1) := by
    simpa only [mul_assoc, mul_comm 2 N] using
      (mul_le_mul_of_nonneg_left (by linarith : a + 2 ≤ 2 * (a + 1)) hN)
  calc
    Real.log (N * (a + 2)) ≤ (N * (a + 2)) ^ (1/2 : ℝ) / (1/2 : ℝ) :=
      Real.log_le_rpow_div (by positivity) (by norm_num)
    _ ≤ ((2 * N) * (a + 1)) ^ (1/2 : ℝ) / (1/2 : ℝ) :=
      div_le_div_of_nonneg_right (Real.rpow_le_rpow (by positivity) h (by norm_num)) (by norm_num)
    _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity)]; ring

/-- The zero statistic in §2.3 converges absolutely for the paper's decay bound. -/
theorem zeroStatistic_summable_norm (c : CitedFacts) (f : ℝ → ℝ) (d : ℤ) (X : ℝ)
    (hd : IsFundDisc d) (hd' : 1 < |d|) (hX : 1 < X)
    (hf : ∃ C : ℝ, ∀ x, |f x| ≤ C / (1 + x^2)) :
    Summable fun z : ZeroCopy d => ‖zeroSummand f d X z‖ := by
  classical
  obtain ⟨C, hC⟩ := hf
  have hC₀ : 0 ≤ C := by
    have h := hC 0
    simp at h
    exact (abs_nonneg _).trans h
  obtain ⟨M, hM, hcount⟩ := c.zeroCount
  let q := Real.log X / (2 * Real.pi)
  have hq : 0 < q := div_pos (Real.log_pos hX) (by positivity)
  let B := 2 * C / min 1 (q ^ 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let K := 2 * (2 * (d.natAbs : ℝ)) ^ (1/2 : ℝ) * M * B
  let band := halfOpenZeroBand d
  have hclosed (n : ℕ) := hcount d hd hd' n (Nat.cast_nonneg n)
  have hfinite (n : ℕ) : (band n).Finite :=
    (hclosed n).1.subset (halfOpenZeroBand_subset d n)
  letI (n : ℕ) : Fintype (band n) := (hfinite n).fintype
  apply (summable_partition (f := fun z : ZeroCopy d => ‖zeroSummand f d X z‖)
    (fun _ => norm_nonneg _) (halfOpenZeroBand_partition d)).2
  constructor
  · exact fun n => (hasSum_fintype (L := SummationFilter.unconditional (band n)) _).summable
  · have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(3/2) : ℝ)) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    have hs' : Summable (fun n : ℕ => K * ((n : ℝ) + 1) ^ (-(3/2) : ℝ)) := by
      simpa [Nat.cast_add] using ((summable_nat_add_iff 1).mpr hs).mul_left K
    refine Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun _ => norm_nonneg _)) ?_ hs'
    intro n
    have hcard : (Fintype.card (band n) : ℝ) ≤ M * Real.log ((d.natAbs : ℝ) * (n + 2)) := by
      rw [← Set.toFinset_card, ← Set.ncard_eq_toFinset_card']
      exact (Nat.cast_le.mpr (Set.ncard_le_ncard (halfOpenZeroBand_subset d n)
        (hclosed n).1)).trans (hclosed n).2
    have hterm (z : band n) :
        ‖zeroSummand f d X z‖ ≤ B / ((n : ℝ) + 1)^2 := by
      simp only [Real.norm_eq_abs, zeroSummand, mul_div_assoc]
      have hcast : (n : ℝ) ≤ |z.val.ordinate| := z.property.1
      exact (hC (z.val.ordinate * q)).trans (decay_bound hC₀ hq (Nat.cast_nonneg n) hcast)
    have hn : 0 < (n : ℝ) + 1 := by positivity
    calc
      (∑' z : band n, ‖zeroSummand f d X z‖)
          = ∑ z : band n, ‖zeroSummand f d X z‖ := tsum_fintype _
      _ ≤ ∑ _z : band n, B / ((n : ℝ) + 1)^2 := Finset.sum_le_sum (fun z _ => hterm z)
      _ = (Fintype.card (band n) : ℝ) * (B / ((n : ℝ) + 1)^2) := by simp
      _ ≤ (M * Real.log ((d.natAbs : ℝ) * (n + 2))) * (B / ((n : ℝ) + 1)^2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ (M * (2 * (2 * (d.natAbs : ℝ)) ^ (1/2 : ℝ) * ((n : ℝ) + 1) ^ (1/2 : ℝ))) *
          (B / ((n : ℝ) + 1)^2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (log_growth_bound (Nat.cast_nonneg _) n (Nat.cast_nonneg n)) hM.le)
          (by positivity)
      _ = K * ((n : ℝ) + 1) ^ (-(3/2) : ℝ) := by
        have he : ((n : ℝ) + 1) ^ (-(3/2) : ℝ) =
            ((n : ℝ) + 1) ^ (1/2 : ℝ) * (((n : ℝ) + 1)^2)⁻¹ := by
          rw [show (-(3/2) : ℝ) = 1/2 + (- (2 : ℝ)) by norm_num,
            Real.rpow_add hn, Real.rpow_neg hn.le, Real.rpow_two]
        rw [he]
        simp only [K, div_eq_mul_inv]
        ac_rfl

theorem zeroStatistic_summable (c : CitedFacts) (f : ℝ → ℝ) (d : ℤ) (X : ℝ)
    (hd : IsFundDisc d) (hd' : 1 < |d|) (hX : 1 < X)
    (hf : ∃ C : ℝ, ∀ x, |f x| ≤ C / (1 + x^2)) :
    Summable (zeroSummand f d X) :=
  (zeroStatistic_summable_norm c f d X hd hd' hX hf).of_norm

/-- Under the stated GRH, the zeros used by the statistic lie on the critical line. -/
theorem zeroCopy_re (hGRH : DirichletLZerosOnLine) {d : ℤ} (hd : 1 < |d|) (z : ZeroCopy d) :
    z.1.val.re = 1 / 2 := by
  letI : NeZero d.natAbs := ⟨by have := natAbs_gt_one hd; omega⟩
  obtain ⟨hs₀, hs₁, hz⟩ := z.1.property
  rw [quadraticL_eq] at hz
  exact hGRH d.natAbs (chi d) z.1.val hs₀ hs₁ hz

end Chowla

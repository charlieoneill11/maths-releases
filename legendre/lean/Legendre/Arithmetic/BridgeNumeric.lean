import Legendre.Arithmetic.Log
import Legendre.Arithmetic.TenthRoot
import Legendre.BridgeData

namespace Legendre.Arithmetic

open scoped BigOperators

private def u₁ : ℚ := 1 + 1 / 10 ^ 10

private theorem cast_u₁ : (u₁ : ℝ) = U₁ := by simp [u₁, U₁]

private def scaleLower (row : BridgeRow) : ℚ :=
  1.1 * (tenthRoot row.lo).lo * ((row.lo : ℚ) / ((row.lo : ℚ) + 1))

private def valueLog (row : BridgeRow) : Bounds :=
  logBounds (((row.lo : ℚ) + 1) / 1.1)

/-- Rational comparisons for conditions (i), (ii), (iv), and (v) in Table 1. -/
def rowBaseChecker (row : BridgeRow) : Bool :=
  decide (
    0 < row.lo ∧ 0 < row.scaleLo ∧ 0 ≤ row.k ∧
    row.logLo < 1.1 * (logBounds row.lo).lo ∧
    1.1 * (logBounds ((row.hi : ℚ) + 1)).hi < row.logHi ∧
    row.scaleLo < scaleLower row ∧
    4000 * u₁ * 10 ^ 12 < row.scaleLo * (row.lo : ℚ) * (tenthRoot row.lo).lo ∧
    row.k < 1.00000063 - row.chargeHi ∧
    row.valueLo < row.k * scaleLower row - 0.765870 * (valueLog row).hi + 1.37957 ∧
    row.derivLo < row.k * (scaleLower row / 10) - 0.765870)

structure RowBaseBounds (row : BridgeRow) : Prop where
  scale_pos : 0 < row.scaleLo
  logLo : (row.logLo : ℝ) < 1.1 * Real.log row.lo
  logHi : 1.1 * Real.log ((row.hi : ℝ) + 1) < (row.logHi : ℝ)
  scaleLo : (row.scaleLo : ℝ) < 1.1 * (row.lo : ℝ) ^ ((1 : ℝ) / 10) *
    ((row.lo : ℝ) / ((row.lo : ℝ) + 1))
  lengthLo : 4000 * U₁ * 10 ^ 12 < (row.scaleLo : ℝ) * (row.lo : ℝ) *
    (row.lo : ℝ) ^ ((1 : ℝ) / 10)
  pole : (row.k : ℝ) < 1.00000063 - (row.chargeHi : ℝ)
  comparison : (row.valueLo : ℝ) < bridgeComparison row.k row.lo
  derivative : (row.derivLo : ℝ) < 0.11 * (row.k : ℝ) * (row.lo : ℝ) ^ ((1 : ℝ) / 10) *
    ((row.lo : ℝ) / ((row.lo : ℝ) + 1)) - 0.765870

theorem rowBaseChecker_sound (row : BridgeRow) (h : rowBaseChecker row = true) :
    RowBaseBounds row := by
  unfold rowBaseChecker at h
  obtain ⟨hl, hP, hk, hlogLo, hlogHi, hscale, hlength, hpole, hvalue, hderiv⟩ :=
    of_decide_eq_true h
  have hlo := (logBounds_sound row.lo (by exact_mod_cast hl)).1
  have hhi := (logBounds_sound ((row.hi : ℚ) + 1) (by positivity)).2
  have hroot := (tenthRoot_sound row.lo).1
  have hlo' : ((logBounds row.lo).lo : ℝ) ≤ Real.log row.lo := by simpa using hlo
  have hhi' : Real.log ((row.hi : ℝ) + 1) ≤ ((logBounds ((row.hi : ℚ) + 1)).hi : ℝ) := by
    simpa using hhi
  have hvalueLog : Real.log (((row.lo : ℝ) + 1) / 1.1) ≤ ((valueLog row).hi : ℝ) := by
    simpa [valueLog] using (logBounds_sound (((row.lo : ℚ) + 1) / 1.1) (by positivity)).2
  have hL : (scaleLower row : ℝ) ≤ 1.1 * (row.lo : ℝ) ^ ((1 : ℝ) / 10) *
      ((row.lo : ℝ) / ((row.lo : ℝ) + 1)) := by
    push_cast [scaleLower]
    gcongr
  have hlen : (row.scaleLo : ℝ) * (row.lo : ℝ) * ((tenthRoot row.lo).lo : ℝ) ≤
      (row.scaleLo : ℝ) * (row.lo : ℝ) * (row.lo : ℝ) ^ ((1 : ℝ) / 10) := by
    have hP' : (0 : ℝ) < row.scaleLo := Rat.cast_pos.mpr hP
    gcongr
  have hk' : (0 : ℝ) ≤ row.k := Rat.cast_nonneg.mpr hk
  refine ⟨hP, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h' := (Rat.cast_lt (K := ℝ)).mpr hlogLo
    push_cast at h'
    exact h'.trans_le (mul_le_mul_of_nonneg_left hlo' (by norm_num))
  · have h' := (Rat.cast_lt (K := ℝ)).mpr hlogHi
    push_cast at h'
    exact (mul_le_mul_of_nonneg_left hhi' (by norm_num)).trans_lt h'
  · exact ((Rat.cast_lt (K := ℝ)).mpr hscale).trans_le hL
  · have h' := (Rat.cast_lt (K := ℝ)).mpr hlength
    push_cast at h'
    rw [cast_u₁] at h'
    exact h'.trans_le hlen
  · have h' := (Rat.cast_lt (K := ℝ)).mpr hpole
    push_cast at h'
    exact h'
  · have h' := (Rat.cast_lt (K := ℝ)).mpr hvalue
    push_cast at h'
    unfold bridgeComparison
    have hmul := mul_le_mul_of_nonneg_left hL hk'
    have hlog := mul_le_mul_of_nonneg_left hvalueLog (by norm_num : 0 ≤ (0.765870 : ℝ))
    linarith
  · have h' := (Rat.cast_lt (K := ℝ)).mpr hderiv
    push_cast at h'
    have hmul := mul_le_mul_of_nonneg_left hL hk'
    linarith

private def prefixLength (j : ℕ) : ℚ := (j : ℚ) / 4000

/-- Directed lower bound on `log (P₀ vⱼ) - log U₁`. -/
def rowOffset (row : BridgeRow) (j : ℕ) : ℚ :=
  (logBounds (row.scaleLo * prefixLength j)).lo - (logBounds u₁).hi

theorem rowOffset_le (row : BridgeRow) (hP : 0 < row.scaleLo) (j : ℕ) (hj : 1 ≤ j) :
    (rowOffset row j : ℝ) ≤ Real.log ((row.scaleLo : ℝ) * ((j : ℝ) / 4000)) - Real.log U₁ := by
  have hj₀ : 0 < (j : ℚ) := by exact_mod_cast (show 0 < j by omega)
  have hlo := (logBounds_sound (row.scaleLo * prefixLength j) (by
    unfold prefixLength
    positivity)).1
  have hhi := (logBounds_sound u₁ (by norm_num [u₁])).2
  have hs := sub_le_sub hlo hhi
  simpa [rowOffset, prefixLength, cast_u₁] using hs

private def rowChargeExactTerm (row : BridgeRow) (e : ℕ → ℚ) (j : ℕ) : ℚ :=
  let b := rowOffset row j
  let L := if 0 ≤ b then row.logHi else row.logLo
  8 * u₁ ^ 2 * ((e j - e (j + 1)) * prefixLength j * L / (L + b))

private def rowChargeUpperTerm (row : BridgeRow) (e : ℕ → ℚ) (j : ℕ) : ℚ :=
  if e (j + 1) < e j then roundUp (10 ^ 20) (rowChargeExactTerm row e j) else 0

/-- The outward-rounded sum of the strict drops in the step heights. -/
def rowChargeUpper (row : BridgeRow) (e : ℕ → ℚ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 4000, rowChargeUpperTerm row e j

/-- Check positive denominators for strict drops and the rounded sum of their charges. -/
def rowChargeChecker (row : BridgeRow) (e : ℕ → ℚ) : Bool :=
  (List.range 4000).all (fun i ↦
    let j := i + 1
    decide (e (j + 1) < e j → 0 < row.logLo + rowOffset row j)) &&
  decide (rowChargeUpper row e < row.chargeHi)

private theorem rowChargeExactTerm_cast (row : BridgeRow) (e : ℕ → ℚ) (j : ℕ) :
    (rowChargeExactTerm row e j : ℝ) =
      let b := (rowOffset row j : ℝ)
      let L : ℝ := if 0 ≤ b then row.logHi else row.logLo
      8 * U₁ ^ 2 * (((e j : ℝ) - (e (j + 1) : ℝ)) * ((j : ℝ) / 4000) * L / (L + b)) := by
  by_cases hb : 0 ≤ rowOffset row j
  · have hb' : (0 : ℝ) ≤ rowOffset row j := Rat.cast_nonneg.mpr hb
    simp [rowChargeExactTerm, prefixLength, cast_u₁, hb, hb']
  · have hb' : ¬ (0 : ℝ) ≤ rowOffset row j := fun h => hb (Rat.cast_nonneg.mp h)
    simp [rowChargeExactTerm, prefixLength, cast_u₁, hb, hb']

theorem rowChargeChecker_sound (row : BridgeRow) (e : ℕ → ℚ) (he : ShoulderSteps e)
    (hbase : rowBaseChecker row = true) (hcharge : rowChargeChecker row e = true) :
    BridgeRowChecks row e (fun j ↦ (rowOffset row j : ℝ)) := by
  have hb := rowBaseChecker_sound row hbase
  unfold rowChargeChecker at hcharge
  obtain ⟨hpos, hsum⟩ := Bool.and_eq_true_iff.mp hcharge
  have hsum := of_decide_eq_true hsum
  refine ⟨hb.logLo, hb.logHi, hb.scaleLo, hb.lengthLo, ?_, ?_, hb.pole, hb.comparison, hb.derivative⟩
  · intro j hj hdrop
    have hji := Finset.mem_Icc.mp hj
    refine ⟨rowOffset_le row hb.scale_pos j hji.1, ?_⟩
    have hall := (List.all_eq_true.mp hpos) (j - 1) (List.mem_range.mpr (by omega))
    have hj' : j - 1 + 1 = j := by omega
    dsimp only at hall
    rw [hj'] at hall
    have h := (Rat.cast_pos (K := ℝ)).mpr ((of_decide_eq_true hall) hdrop)
    simpa using h
  · have hsum' := (Rat.cast_lt (K := ℝ)).mpr hsum
    unfold rowChargeUpper at hsum'
    rw [Rat.cast_sum] at hsum'
    apply lt_of_le_of_lt _ hsum'
    unfold shoulderCharge
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    change _ ≤ (rowChargeUpperTerm row e j : ℝ)
    rw [← rowChargeExactTerm_cast]
    apply Rat.cast_le.mpr
    by_cases hdrop : e (j + 1) < e j
    · simp only [rowChargeUpperTerm, if_pos hdrop]
      exact le_roundUp _ (by positivity) _
    · have hji := Finset.mem_Icc.mp hj
      have heq := le_antisymm (he.antitone j hji.1 hji.2) (le_of_not_gt hdrop)
      simp [rowChargeUpperTerm, rowChargeExactTerm, heq]

/-- Directed bounds used in the uniform error estimate in Proposition 22. -/
structure BridgeErrorData where
  minSqrt : ℚ
  maxD : ℚ
  minD : ℚ
  log2Lo : ℚ
  logArgHi : ℚ

def bridgeErrorData : BridgeErrorData where
  minSqrt := (35 * 10 ^ 12) * (tenthRoot (35 * 10 ^ 12)).lo
  maxD := 1.1 / (35 * 10 ^ 12)
  minD := 1.1 / (6 * 10 ^ 14 + 1)
  log2Lo := (logBounds 2).lo
  logArgHi := (logBounds (7 / (1.1 / (6 * 10 ^ 14 + 1)))).hi

theorem bridgeMinSqrt_le : (bridgeErrorData.minSqrt : ℝ) ≤
    (35 * 10 ^ 12 : ℝ) * (35 * 10 ^ 12 : ℝ) ^ ((1 : ℝ) / 10) := by
  have h := (tenthRoot_sound (35 * 10 ^ 12)).1
  have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (35 * 10 ^ 12 : ℝ))
  norm_num [bridgeErrorData] at h' ⊢
  exact h'

theorem bridgeLog2Lo_le : (bridgeErrorData.log2Lo : ℝ) ≤ Real.log 2 := by
  simpa [bridgeErrorData] using (logBounds_sound 2 (by norm_num)).1

theorem bridgeLogArg_le : Real.log (7 / (bridgeErrorData.minD : ℝ)) ≤
    (bridgeErrorData.logArgHi : ℝ) := by
  have h := (logBounds_sound (7 / (1.1 / (6 * 10 ^ 14 + 1))) (by norm_num)).2
  push_cast at h
  simpa [bridgeErrorData] using h

private def u : ℚ := 1 + 1 / 10 ^ 12

private theorem cast_u : (u : ℝ) = U := by simp [u, U]

def primePowerErrorBound (d : BridgeErrorData) : ℚ :=
  (2 + (76 / d.log2Lo) * (1 + 68 * u)) * 76 * u / d.minSqrt

def zeroErrorBound (d : BridgeErrorData) : ℚ :=
  2 * d.maxD * ((3 + 0.15 * d.logArgHi) * 625 + 300 + 4)

def shoulderEndpointErrorBound (d : BridgeErrorData) : ℚ :=
  4 * u ^ 2 * 0.76 * 37.5 / d.minSqrt

def bridgeErrorChecker (d : BridgeErrorData) : Bool :=
  decide (0 < d.minSqrt ∧ 0 < d.maxD ∧ 0 < d.minD ∧ 0 < d.log2Lo ∧ 0 ≤ d.logArgHi ∧
    primePowerErrorBound d < 7.3 / 10 ^ 10 ∧
    zeroErrorBound d < 3.6 / 10 ^ 10 ∧
    shoulderEndpointErrorBound d < 1.5 / 10 ^ 13 ∧
    primePowerErrorBound d + zeroErrorBound d + shoulderEndpointErrorBound d + 1 / 10 ^ 12 <
      1.1 / 10 ^ 9)

structure CertifiedBridgeErrors (d : BridgeErrorData) : Prop where
  minSqrt_pos : (0 : ℝ) < d.minSqrt
  maxD_pos : (0 : ℝ) < d.maxD
  minD_pos : (0 : ℝ) < d.minD
  log2Lo_pos : (0 : ℝ) < d.log2Lo
  logArgHi_nonneg : (0 : ℝ) ≤ d.logArgHi
  prime_power : (primePowerErrorBound d : ℝ) < 7.3 / 10 ^ 10
  zeros : (zeroErrorBound d : ℝ) < 3.6 / 10 ^ 10
  endpoints : (shoulderEndpointErrorBound d : ℝ) < 1.5 / 10 ^ 13
  total : (2 + (76 / (d.log2Lo : ℝ)) * (1 + 68 * U)) * 76 * U / (d.minSqrt : ℝ) +
    2 * (d.maxD : ℝ) * ((3 + 0.15 * (d.logArgHi : ℝ)) * 625 + 300 + 4) +
    4 * U ^ 2 * 0.76 * 37.5 / (d.minSqrt : ℝ) + 1 / 10 ^ 12 < 1.1 / 10 ^ 9

theorem bridgeErrorChecker_sound (d : BridgeErrorData) (h : bridgeErrorChecker d = true) :
    CertifiedBridgeErrors d := by
  unfold bridgeErrorChecker at h
  obtain ⟨hroot, hmax, hmin, hlog2, hlog, hpow, hzero, hendpoint, htotal⟩ := of_decide_eq_true h
  refine ⟨Rat.cast_pos.mpr hroot, Rat.cast_pos.mpr hmax, Rat.cast_pos.mpr hmin,
    Rat.cast_pos.mpr hlog2, Rat.cast_nonneg.mpr hlog, ?_, ?_, ?_, ?_⟩
  · simpa using (Rat.cast_lt (K := ℝ)).mpr hpow
  · simpa using (Rat.cast_lt (K := ℝ)).mpr hzero
  · simpa using (Rat.cast_lt (K := ℝ)).mpr hendpoint
  · simpa [primePowerErrorBound, zeroErrorBound, shoulderEndpointErrorBound, cast_u] using
      (Rat.cast_lt (K := ℝ)).mpr htotal

theorem firstRow_base_verified : rowBaseChecker firstRow = true := by decide +kernel

theorem secondRow_base_verified : rowBaseChecker secondRow = true := by decide +kernel

theorem bridge_errors_verified : bridgeErrorChecker bridgeErrorData = true := by decide +kernel

theorem bridge_errors : CertifiedBridgeErrors bridgeErrorData :=
  bridgeErrorChecker_sound _ bridge_errors_verified

end Legendre.Arithmetic

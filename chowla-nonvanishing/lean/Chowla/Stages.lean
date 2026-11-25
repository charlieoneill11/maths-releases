import Chowla.Model.Inner
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Chowla

def stageProportion : Fin 8 → ℚ := ![
  0.94531427448210, 0.945321516147, 0.945325433280444, 0.945325784098260,
  0.94532732177059, 0.9453286989, 0.9453391726, 0.9453419890]

def initialStageRows (n : ℕ) : List Rows.RowData :=
  Rows.r0 ++ Rows.r1Grid ++ Rows.r1Modes ++ Rows.r2 ++
    (if 2 ≤ n then Rows.r3 else []) ++ (if 3 ≤ n then Rows.r4 else []) ++
    (if 4 ≤ n then Rows.r5 else [])

def stageRows (i : Fin 8) : List Rows.RowData :=
  if i.val < 4 then initialStageRows (i.val + 1) else
    ((initialStageRows 4).map fun r => { r with weight := Rows.inheritedWeight * r.weight }) ++
      Rows.r6 ++ (if 5 ≤ i.val then Rows.r7 else []) ++
      (if 6 ≤ i.val then Rows.r8 else []) ++ (if 7 ≤ i.val then Rows.r9 else [])

noncomputable def stageAmplitude (i : Fin 8) : Amplitude :=
  (stageRows i).map Rows.RowData.toRow

def p₀ : ℚ := (19 - 3.916317365) / 16

noncomputable def certificateQ (F : Amplitude) : ℝ :=
  (p₀ : ℝ) + inner_G F - inner F F / 2

structure StageBounds where
  lowerCentral : ℚ
  upperCentral : ℚ
  upperGram : ℚ
  lowerProportion : ℚ
  deriving DecidableEq

/-- Exact rational comparisons after the corresponding bounds have been proved. -/
def StageBounds.check (i : Fin 8) (b : StageBounds) : Bool :=
  if i.val < 4 then
    decide (0 < b.lowerCentral ∧ 0 < b.upperGram ∧
      stageProportion i < p₀ + b.lowerCentral ^ 2 / (2 * b.upperGram))
  else decide (stageProportion i < b.lowerProportion)

/-- The bounds required of the rational evaluator for the paper's stage i + 1. -/
def StageBounds.Sound (i : Fin 8) (b : StageBounds) : Prop :=
  let F := stageAmplitude i
  if i.val < 4 then
    (b.lowerCentral : ℝ) ≤ inner_G F ∧ inner_G F ≤ (b.upperCentral : ℝ) ∧
      inner F F ≤ (b.upperGram : ℝ)
  else (b.lowerProportion : ℝ) ≤ certificateQ F

private theorem stageProportion_gt_p₀ (i : Fin 8) : (p₀ : ℝ) < (stageProportion i : ℝ) := by
  fin_cases i <;> norm_num [p₀, stageProportion]

/-- Proposition 32 in the form used by stages 1–4. The Gram value may have any sign. -/
theorem early_stage_gain (i : Fin 8) (hi : i.val < 4) (b : StageBounds)
    (hs : b.Sound i) (hc : b.check i = true) :
    0 < inner_G (stageAmplitude i) ∧
      2 * ((stageProportion i : ℝ) - (p₀ : ℝ)) * inner (stageAmplitude i) (stageAmplitude i) <
        inner_G (stageAmplitude i) ^ 2 := by
  have hs' := hs
  simp only [StageBounds.Sound, if_pos hi] at hs'
  have hc' := hc
  simp only [StageBounds.check, if_pos hi, decide_eq_true_eq] at hc'
  have hcl : (0 : ℝ) < b.lowerCentral := by exact_mod_cast hc'.1
  have hdu : (0 : ℝ) < b.upperGram := by exact_mod_cast hc'.2.1
  have hgain : (stageProportion i : ℝ) < (p₀ : ℝ) + (b.lowerCentral : ℝ)^2 / (2 * (b.upperGram : ℝ)) := by
    exact_mod_cast hc'.2.2
  have hC := hcl.trans_le hs'.1
  refine ⟨hC, ?_⟩
  let g := (stageProportion i : ℝ) - (p₀ : ℝ)
  have hg : 0 < g := sub_pos.mpr (stageProportion_gt_p₀ i)
  have hgain' : g < (b.lowerCentral : ℝ)^2 / (2 * (b.upperGram : ℝ)) := by
    dsimp [g]
    linarith
  have hcross := (lt_div_iff₀ (by positivity : 0 < 2 * (b.upperGram : ℝ))).mp hgain'
  calc
    _ ≤ 2 * g * (b.upperGram : ℝ) :=
      mul_le_mul_of_nonneg_left hs'.2.2 (by positivity)
    _ < (b.lowerCentral : ℝ)^2 := by linarith
    _ ≤ _ := pow_le_pow_left₀ hcl.le hs'.1 2

/-- Proposition 32 in the form used by stages 5–8. -/
theorem late_stage_gain (i : Fin 8) (hi : 4 ≤ i.val) (b : StageBounds)
    (hs : b.Sound i) (hc : b.check i = true) :
    (stageProportion i : ℝ) < certificateQ (stageAmplitude i) := by
  have hn := Nat.not_lt.mpr hi
  simp only [StageBounds.Sound, if_neg hn] at hs
  simp only [StageBounds.check, if_neg hn, decide_eq_true_eq] at hc
  exact (show (stageProportion i : ℝ) < (b.lowerProportion : ℝ) by exact_mod_cast hc).trans_le hs

/-- The update for the running bound when a new list of rows is appended. -/
theorem certificateQ_append (F F' : Amplitude) :
    certificateQ (F ++ F') =
      certificateQ F + inner_G F' - inner F F' - inner F' F' / 2 := by
  simp only [certificateQ, inner_G, List.map_append, List.sum_append,
    inner_append_left, inner_append_right]
  rw [inner_comm F' F]
  ring

/-- The early-stage central upper enclosure controls the inherited Gram value. -/
theorem early_gram_bound (i : Fin 8) (hi : i.val < 4) (b : StageBounds)
    (hs : b.Sound i) (hc : b.check i = true) :
    inner (stageAmplitude i) (stageAmplitude i) <
      (b.upperCentral : ℝ)^2 / (2 * ((stageProportion i : ℝ) - (p₀ : ℝ))) := by
  obtain ⟨hC, hgain⟩ := early_stage_gain i hi b hs hc
  have hbound := hs
  simp only [StageBounds.Sound, if_pos hi] at hbound
  have hg := sub_pos.mpr (stageProportion_gt_p₀ i)
  apply (lt_div_iff₀ (mul_pos (by norm_num) hg)).mpr
  have hu := pow_le_pow_left₀ hC.le hbound.2.1 2
  linarith


theorem stageAmplitude_last : stageAmplitude 7 = F₈ := by
  simp [stageAmplitude, stageRows, initialStageRows, F₈, finalRows]

/-- Finishing the certificate from the verified enclosure at stage eight and Lemma 31. -/
theorem certificate_of_final_bounds (b : StageBounds) (hs : b.Sound 7) (hc : b.check 7 = true)
    (hcot : Real.cot (1 / 4) < 3.916317365) : CertificateStatement := by
  have h := late_stage_gain 7 (by decide) b hs hc
  rw [stageAmplitude_last] at h
  have hlast : (stageProportion 7 : ℝ) = 0.9453419890 := by
    change ((0.9453419890 : ℚ) : ℝ) = 0.9453419890
    norm_num
  rw [hlast] at h
  have h₀ : (p₀ : ℝ) = (19 - 3.916317365) / 16 := by norm_num [p₀]
  unfold certificateQ at h
  rw [h₀] at h
  unfold CertificateStatement
  linarith

end Chowla

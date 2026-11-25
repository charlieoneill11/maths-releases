import HadwigerNelson.Centres.BudgetDefs
import Mathlib.Analysis.Real.Pi.Bounds

namespace HadwigerNelson.Centres
open Crossings
noncomputable section

abbrev degreeCap (n m h : ℕ) := weightedBound n m h 0 1 0
abbrev budgetR (n m s : ℕ) :=
  min (degreeCap n m s) (min ((5*s+s.choose 2 : ℕ):ℝ) ((degreeCap n m s+5*s)/2))
abbrev budgetD (n m s j : ℕ) :=
  min (degreeCap n m (s+j)) (min ((14*s+8*j+s.choose 2:ℕ):ℝ) ((degreeCap n m (s+j)+5*(s+j:ℕ))/2))

private def single (n m h : ℕ) (t L : ℝ) (i : Fin 7) :=
  let K := diskLimit i
  let B : ℝ := ((K-1)*(n-h)/2 : ℕ) + min (2*L) (K*h+h.choose 2 : ℕ)
  2*(m:ℝ)-2*t-B

private def charge (n m h : ℕ) (t L z : ℝ) :=
  (∑ i : Fin 7, excessWidth i * max (single n m h t L i - z) 0)/2

private theorem width_nonneg (i : Fin 7) : 0≤excessWidth i := by
  unfold excessWidth; split <;> norm_num

private theorem charge_nonneg (n m h : ℕ) (t L z : ℝ) : 0≤charge n m h t L z :=
  div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (width_nonneg i) (le_max_right ..)) (by norm_num)

private theorem correction (n m h : ℕ) {t₀ t L₀ L z₀ z : ℝ}
    (ht : t₀≤t) (hL : L≤L₀) (hz : z≤z₀) :
    charge n m h t₀ L₀ z₀ ≤ charge n m h t L z + (t-t₀)*(∑ i : Fin 7,excessWidth i) := by
  let gain := t-t₀
  have each (i : Fin 7) : max (single n m h t₀ L₀ i-z₀) 0 ≤ max (single n m h t L i-z) 0 + 2*gain := by
    have grow : min (2*L) (((diskLimit i)*h+h.choose 2:ℕ):ℝ) ≤ min (2*L₀) _ :=
      min_le_min_right _ (by linarith)
    have bound := le_max_left (single n m h t L i-z) 0
    have zero := le_max_right (single n m h t L i-z) 0
    dsimp [single] at *
    dsimp [gain]
    apply max_le <;> linarith
  have sum := Finset.sum_le_sum (s:=Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_left (each i) (width_nonneg i)
  simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul] at sum
  unfold charge
  dsimp [gain] at sum
  linarith only [sum]

private theorem rates (p : Profile) :
    0≤smallIntercept p ∧ 0 ≤ intercept p-smallIntercept p ∧ 0≤angleCost p ∧
      angleCost p*(∑ i : Fin 7,excessWidth i) ≤ intercept p := by
  have diff : Profile.fine ≠ Profile.coarse := by intro e; cases e
  cases p <;> norm_num [smallIntercept,intercept,angleCost,excessWidth,Fin.sum_univ_succ,diff]

/-- Substitution of the degree and crossing estimates. Lowering the doubled
pair count by one costs at most the sum of the seven excess widths in the
angular budget, which is paid by one full intercept. -/
theorem score_from_orientation (n m s j t : ℕ) (p : Profile) (L A B ex total : ℝ)
    (hsize : s+j≤n) (hL : L≤degreeCap n m (s+j)) (ht : pairLower n m≤t)
    (ca : (t:ℝ)-budgetR n m s-L/2≤A) (cb : (t:ℝ)-budgetD n m s j-L/2≤B)
    (u : ex≤angularBudget n m t (s+j) L (budgetR n m s) (budgetD n m s j))
    (nnA : 0≤A) (nnB : 0≤B) (nn : 0≤total)
    (raw : smallIntercept p*A+(intercept p-smallIntercept p)*B-angleCost p*ex≤total) :
    profileCredit n m s j (intercept p) (smallIntercept p) (angleCost p) ≤ total := by
  let h := s+j
  let L₀ := degreeCap n m h
  let r := budgetR n m s
  let d := budgetD n m s j
  let t₀ := pairLower n m
  let I := intercept p
  let IR := smallIntercept p
  let J := angleCost p
  let reserve := ((m:ℝ)-r)*δR+((m:ℝ)-d)*(δ-δR)
  let Q := (355/113:ℝ)*n-reserve
  let QD := (355/113:ℝ)*(n-h:ℕ)-reserve+δ*L₀/2
  let x := t₀-r-L₀/2
  let y := t₀-d-L₀/2
  let G := ((t:ℝ)-t₀)*(∑ i : Fin 7,excessWidth i)
  let Qstar := min (Q-charge n m h t₀ L₀ 0) (QD-charge n m h t₀ L₀ L₀)
  have same0 (q L : ℝ) : (∑ i : Fin 7,excessWidth i*max (single n m h q L i) 0)/2=charge n m h q L 0 := by simp [charge]
  change max 0 (max (IR*max x 0+(I-IR)*max y 0-J*min Q QD)
    (IR*x+(I-IR)*y-J*min (Q-(∑ i : Fin 7,excessWidth i*max (single n m h t₀ L₀ i) 0)/2)
      (QD-charge n m h t₀ L₀ L₀))) ≤ total
  rw [same0]
  let Qr := Real.pi*n-((m:ℝ)-r)*δR-((m:ℝ)-d)*(δ-δR)
  have qnorm : Qr=Real.pi*n-reserve := by dsimp [Qr,reserve]; ring
  change ex ≤ min (Qr-(∑ i : Fin 7,excessWidth i*max (single n m h t L i) 0)/2)
    ((Qr-Real.pi*h+δ*L/2)-charge n m h t L L) at u
  rw [qnorm,same0,le_min_iff] at u
  have πrate : Real.pi≤355/113 := by linarith [Real.pi_lt_d20]
  have u₁ : ex ≤ Q-charge n m h t L 0 := by
    dsimp [Q]
    linarith [mul_le_mul_of_nonneg_right πrate (Nat.cast_nonneg n),u.1]
  have refD : Real.pi*n-reserve-Real.pi*h+δ*L/2≤QD := by
    have l : δ*L≤δ*L₀ := mul_le_mul_of_nonneg_left hL (by norm_num [δ])
    have nh : h≤n := hsize
    have pi := mul_le_mul_of_nonneg_right πrate (Nat.cast_nonneg (n-h) (α:=ℝ))
    rw [Nat.cast_sub nh] at pi
    dsimp [QD]; rw [Nat.cast_sub nh]
    linarith
  have u₂ : ex≤QD-charge n m h t L L := u.2.trans (sub_le_sub_right refD _)
  have rough : ex≤min Q QD := le_min (by linarith [u₁,charge_nonneg n m h t L 0])
    (by linarith [u₂,charge_nonneg n m h t L L])
  have fine : ex≤Qstar+G := by
    have a := correction n m h ht hL (le_rfl : (0:ℝ)≤0)
    have b := correction n m h ht hL hL
    rw [show Qstar+G = min ((Q-charge n m h t₀ L₀ 0)+G) ((QD-charge n m h t₀ L₀ L₀)+G) from (min_add_add_right ..).symm]
    dsimp only [G,t₀,L₀] at *
    apply le_min <;> linarith
  have ax : x+((t:ℝ)-t₀)≤A := by dsimp [x,r,L₀,h]; linarith
  have by' : y+((t:ℝ)-t₀)≤B := by dsimp [y,d,L₀,h]; linarith
  obtain ⟨ir,dd,jpos,rate⟩ := rates p
  change 0≤IR at ir; change 0≤I-IR at dd; change 0≤J at jpos
  change IR*A+(I-IR)*B-J*ex≤total at raw
  have mx : max x 0≤A := max_le (by dsimp [t₀] at ax; linarith) nnA
  have my : max y 0≤B := max_le (by dsimp [t₀] at by'; linarith) nnB
  apply max_le nn (max_le _ _)
  · linarith only [raw,mul_le_mul_of_nonneg_left mx ir,mul_le_mul_of_nonneg_left my dd,
      mul_le_mul_of_nonneg_left rough jpos]
  · change IR*x+(I-IR)*y-J*Qstar ≤ total
    have pay : J*G ≤ I*((t:ℝ)-t₀) := by
      dsimp [G]
      have r := mul_le_mul_of_nonneg_right rate (sub_nonneg.mpr ht)
      dsimp only [I,J,t₀]
      linarith only [r]
    linarith only [raw,mul_le_mul_of_nonneg_left ax ir,mul_le_mul_of_nonneg_left by' dd,
      mul_le_mul_of_nonneg_left fine jpos,pay]

end
end HadwigerNelson.Centres

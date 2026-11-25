import HadwigerNelson.Stars.Partial.Scores
import HadwigerNelson.Stars.Partial.Local
import HadwigerNelson.Stars.Partial.Degrees

/-! A finite collection of checked source and angular witnesses implies the
uniform physical star gain on the partial wave, including every degree above
the last Fejér certificate. -/
namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (quant)
noncomputable section

private abbrev factor : ℝ := (PartialWave.xInt : ℝ)*quant

private theorem factor_pos : 0 < factor := by norm_num [factor,PartialWave.xInt,quant]

private theorem real_bound (L : Layout.Physical) {d : Nat} (hd : 0<d)
    (k : Fin frequencyCount) (φ : Fin d → ℝ) :
    2/factor*signedSum k.val (powerFraction φ k.val)+4/(factor*d)*nativeSum d ≤
      cellScore PartialWave.datum φ :=
  summed_cell_bound L hd k φ (harmonic_local hd L k) (native_local hd L)

private theorem finite_score (L : Layout.Physical)
    (pass : ∀ p : Fin 4, checkShard p.val=true) {d : Nat} (hd : 0<d) (cap : d≤88)
    (dp : degreePass d=true) (φ : Fin d → ℝ) :
    (901:ℝ)/10^12 ≤ cellScore PartialWave.datum φ := by
  let ids := Data.degree d
  obtain ⟨i,large⟩ := some_frequency hd φ dp
  obtain ⟨_,order,each,_⟩ := degree_facts d hd dp
  obtain ⟨jcap,hk,_,target⟩ := each i
  let j : Fin Data.count := ⟨ids[i.val], jcap⟩
  let q := queryAt ids i.val
  have eq : Data.query j.val=q := by
    have hi : i.val < ids.size := i.isLt
    change Data.query ids[i.val] = Data.query (ids[i.val]?.getD 0)
    rw [Array.getElem?_eq_getElem hi,Option.getD_some]
  let k : Fin frequencyCount := ⟨i.val,i.isLt.trans_le order⟩
  have fs := signed_from_shards pass j
  change (total (Data.query j.val):ℝ) ≤ 10000*signedSum (Data.query j.val).harmonic
    (((Data.query j.val).threshold:ℝ)/10000) at fs
  rw [eq] at fs
  have H : (total q:ℝ) ≤ 10000*signedSum k.val (powerFraction φ k.val) := by
    change q.harmonic=i.val at hk
    rw [hk] at fs
    exact fs.trans (mul_le_mul_of_nonneg_left (signedSum_mono L i.val large) (by norm_num))
  have N := native_from_shards (pass ⟨3,by decide⟩) d hd (by omega)
  have D : 0 < (d:ℝ) := by exact_mod_cast hd
  apply (target_value d hd (Data.native d) (total q) target).trans
  apply le_trans _ (real_bound L hd k φ)
  apply add_le_add
  · calc
      2*(total q:ℝ)/(factor*10000) ≤ 2*(10000*signedSum k.val (powerFraction φ k.val))/(factor*10000) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left H (by norm_num))
          (mul_nonneg factor_pos.le (by norm_num))
      _ = _ := by ring
  · rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left N (by norm_num)) (mul_nonneg factor_pos.le D.le)

private theorem tail_score (L : Layout.Physical) (pass : checkShard 3=true)
    (target : thresholdTarget 89 (Data.native 89) 0=true) {d : Nat} (hd : 89≤d)
    (φ : Fin d → ℝ) : (901:ℝ)/10^12 ≤ cellScore PartialWave.datum φ := by
  have a := target_value 89 (by decide) (Data.native 89) 0 target
  have n := native_from_shards pass 89 (by decide) (by decide)
  have high := native_average_mono L 89 d (by decide) hd
  have mark : 0 ≤ signedSum 0 (powerFraction φ 0) := Finset.sum_nonneg fun
    (i : Fin 132621) _ => mul_nonneg (by exact_mod_cast source_area L (by omega : i.val<136743)) (le_max_left ..)
  apply le_trans _ (real_bound L (by omega) ⟨0,by decide⟩ φ)
  apply le_add_of_nonneg_of_le (mul_nonneg (div_nonneg (by norm_num) factor_pos.le) mark)
  calc
    (901:ℝ)/10^12 ≤ 4*(Data.native 89:ℝ)/(factor*89) := by simpa only [Int.cast_zero,mul_zero,zero_div,zero_add,Nat.cast_ofNat] using a
    _ ≤ 4*nativeSum 89/(factor*89) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left n (by norm_num)) (mul_nonneg factor_pos.le (by norm_num))
    _ = (4/factor)*(nativeSum 89/(89:ℝ)) := by ring
    _ ≤ (4/factor)*(nativeSum d/(d:ℝ)) := mul_le_mul_of_nonneg_left high (div_nonneg (by norm_num) factor_pos.le)
    _ = _ := by ring

/-- Soundness of the four numerical source shards and their exact threshold table. -/
theorem beta_cell_of_checks (L : Layout.Physical)
    (receipts : ∀p : Fin 4,checkShard p.val=true) (checks : dataPass=true)
    {d : Nat} (hd : 0<d) (φ : Fin d → ℝ) :
    (901:ℝ)/10^12 ≤ cellScore PartialWave.datum φ := by
  obtain ⟨deg,high⟩ := data_facts checks
  by_cases small : d≤88
  · exact finite_score L receipts hd small (deg d hd small) φ
  · exact tail_score L (receipts ⟨3,by decide⟩) high (by omega) φ

end
end HadwigerNelson.Stars.PartialCheck

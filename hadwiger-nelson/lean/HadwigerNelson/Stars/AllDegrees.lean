import HadwigerNelson.Stars.DegreeCoverage
import HadwigerNelson.Stars.Fejer
import Mathlib.Analysis.Complex.Norm

namespace HadwigerNelson.Stars.BoxCheck
noncomputable section

/-- The absolute power sum per incident edge. -/
def powerRatio {d : Nat} (z : Fin d → ℂ) (k : Fin harmonics) : ℝ :=
  ‖∑ i, z i^(k.val+1)‖ / d

theorem powerRatio_unit {d : Nat} (z : Fin d → ℂ) (hz : ∀ i, ‖z i‖=1)
    (hd : 0<d) (k : Fin harmonics) : 0 ≤ powerRatio z k ∧ powerRatio z k ≤ 1 := by
  unfold powerRatio
  refine ⟨by positivity,(div_le_one (by exact_mod_cast hd : (0:ℝ)<d)).2 ?_⟩
  have h := norm_sum_le (Finset.univ : Finset (Fin d)) (fun i => z i^(k.val+1))
  simpa only [Complex.norm_pow,hz,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one] using h

theorem powerRatio_fejer {d : Nat} (z : Fin d → ℂ) (hz : ∀ i, ‖z i‖=1) (hd : 0<d) :
    (harmonics+1 : ℝ)/d-1 ≤ ∑ k, fejerWeight harmonics k*(powerRatio z k)^2 := by
  have h (j) : Complex.normSq (z j)=1 := by rw [← Complex.sq_norm,hz]; norm_num
  simpa only [powerRatio,div_pow,Complex.sq_norm] using fejer_bound hd z h harmonics

/-- The box estimate with the paper's degree-dependent choice of rectangles.
For degrees up to 23 it uses every Fourier box and zero native credit. -/
def selectedCredit (rows : Array Row) (sat : Array (Int × Int)) (d : Nat)
    (k : Fin harmonics) (s : ℝ) : ℝ :=
  let q := max 23 d
  boxCredit Finset.univ (fun i : Fin rows.size => areaWeight q rows[i.val])
    (fun i => meanValue rows[i.val]) (fun i => magnitudeValue k.val rows[i.val])
    (nativeValue q (if q == 23 then 0 else nativeNumerator sat q)) s

/-- The five finite tests cover every positive degree. Above 27 the native
credit increases with degree. Below 23 the Fejér lower bound grows. -/
theorem all_degrees_sound (rows : Array Row) (sat : Array (Int × Int)) (d : Nat) (hd : 0<d)
    (z : Fin d → ℂ) (hz : ∀ i, ‖z i‖=1) (score : ℝ)
    (ha : ∀ i : Fin rows.size, 0 ≤ rows[i.val].area)
    (hm : ∀ k : Fin harmonics, ∀ i : Fin rows.size, 0 ≤ magnitudeValue k.val rows[i.val])
    (hsat : ∀ i : Fin sat.size, 0 ≤ sat[i.val].1)
    (box : d ≤ 27 → ∀ k, selectedCredit rows sat d k (powerRatio z k) ≤ score)
    (native : 28 ≤ d → nativeValue d (nativeNumerator sat d) ≤ score)
    (pass : checkData rows sat = true) : (8 : ℝ)/10^9 ≤ score := by
  obtain ⟨degrees,saturated⟩ := checkData_spec rows sat pass
  by_cases small : d ≤ 27
  · let q := max 23 d
    have dl : 23 ≤ q := le_max_left _ _
    have dr : q ≤ 27 := max_le (by decide) small
    apply checkDegree_sound rows sat q (by omega) (powerRatio z) score _ hm
      (powerRatio_unit z hz hd) (box small) _ (degrees q dl dr)
    · intro i
      have hi : (0:ℝ) ≤ rows[i.val].area := by exact_mod_cast ha i
      unfold areaWeight
      split <;> first | exact le_rfl | exact div_nonneg (by positivity) (by norm_num [CompleteWave.xInt])
    · exact (fejer_requirement_antitone hd (le_max_right 23 d)).trans (powerRatio_fejer z hz hd)
  · have big : 28 ≤ d := by omega
    have at28 : (8 : ℝ)/10^9 ≤ nativeValue 28 (nativeNumerator sat 28) := by
      simpa only [nativeValue,Int.cast_zero,mul_zero,zero_div,add_zero] using
        targetPass_sound 28 (by decide) _ 0 saturated
    exact at28.trans ((nativeValue_mono sat hsat (by decide) big).trans (native big))

end
end HadwigerNelson.Stars.BoxCheck

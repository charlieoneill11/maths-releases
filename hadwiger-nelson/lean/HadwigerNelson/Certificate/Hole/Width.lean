import HadwigerNelson.Certificate.Hole.Runtime
import HadwigerNelson.Wave.Geometry.PartialProfile
import HadwigerNelson.Angular.Partial.Profile

namespace HadwigerNelson.Certificate.Hole
open Set
noncomputable section

/-- Interpolation from the 17 positive cells requires only the left wall. -/
theorem scaled_left_cell {W : Wave.Datum} (p : Centres.partialProfile W) (l : ℕ)
    (hl : l<17) {z : ℝ} (hz : z∈Icc ((l:ℝ)*540000000) (((l:ℝ)+1)*540000000)) :
    (10^12:ℝ)*W.left (z/10^12) = Angular.Partial.scaledLeft l z := by
  let u := z/540000000-(l:ℝ)
  have hu : u∈Icc (0:ℝ) 1 := by
    obtain ⟨a,b⟩ := hz; dsimp [u]; constructor <;> linarith
  have a := p.2.2 ⟨l,hl⟩ u hu
  have b := PartialWave.datum_left_segment ⟨l,hl⟩ u hu
  have atZ : (((⟨l,hl⟩ : Fin 17) : ℝ)+u)*54/100000 = z/10^12 := by dsimp [u]; ring
  rw [atZ] at a b
  rw [a.trans b.symm]
  exact Angular.Partial.datum_profile.left_cell l hl hz

private theorem interpDown_floor (z₀ w₀ z₁ w₁ z : ℤ) (hz : z₀<z₁) :
    Arithmetic.interpDown z₀ w₀ z₁ w₁ z = ⌊Arithmetic.linearAt z₀ w₀ z₁ w₁ z⌋ := by
  apply Eq.symm
  apply Int.floor_eq_iff.mpr
  refine ⟨Arithmetic.interpDown_spec _ _ _ _ _ hz,?_⟩
  have h := Arithmetic.real_lt_floorDiv_add_one ((w₁-w₀)*(z-z₀)) (sub_pos.mpr hz)
  simp only [Int.cast_mul,Int.cast_sub] at h
  unfold Arithmetic.linearAt Arithmetic.interpDown
  push_cast
  linarith

private theorem width_nat (n : ℕ) : width (n:ℤ) =
    (if n ≥ PartialWave.y0Int then 0 else
      let i := n/step.toNat
      Arithmetic.interpDown (i*step) (PartialWave.leftKnots[i]?.getD (0,0)).2
        ((i+1)*step) (PartialWave.leftKnots[i+1]?.getD (0,0)).2 n) := by
  rfl

private theorem width_floor_nat (W : Wave.Datum) (p : Centres.partialProfile W) (n : ℕ)
    (hn : n≤9180000000) : width (n:ℤ) = ⌊W.left ((n:ℝ)/10^12)*10^12⌋ := by
  rw [width_nat]
  split_ifs with outside
  · have eq : n=9180000000 := by change n≥9180000000 at outside; omega
    subst n
    rw [W.left_zero _ (by rw [p.2.1]; norm_num [Wave.H,Set.mem_Icc])]
    norm_num
  · change ¬ n≥9180000000 at outside
    let i := n/540000000
    have hi : i<17 := by dsimp [i]; omega
    have lo : i*540000000≤n := by dsimp [i]; omega
    have up : n≤(i+1)*540000000 := by dsimp [i]; omega
    have h := scaled_left_cell p i hi (z:=(n:ℝ)) ⟨by exact_mod_cast lo,by exact_mod_cast up⟩
    rw [mul_comm (W.left _),h]
    change Arithmetic.interpDown _ _ _ _ _ = ⌊Angular.Partial.scaledLeft i n⌋
    have get (j : ℕ) (hj : j<37) : (PartialWave.leftKnots[j]?.getD (0,0))=PartialWave.leftKnot j := by
      rw [getElem?_pos _ _ (by simpa [PartialWave.leftKnots] using hj)]
      exact PartialWave.get_leftKnots j hj
    change Arithmetic.interpDown ((i:ℤ)*step) (PartialWave.leftKnots[i]?.getD (0,0)).2
      (((i:ℤ)+1)*step) (PartialWave.leftKnots[i+1]?.getD (0,0)).2 n = _
    rw [get i (by omega),get (i+1) (by omega),interpDown_floor _ _ _ _ _ (by dsimp [step]; omega)]
    simp [Angular.Partial.scaledLeft,step]

theorem width_floor (W : Wave.Datum) (p : Centres.partialProfile W) (z : ℤ)
    (hz : |z| ≤ cutoff) : width z = ⌊W.left ((z:ℝ)/10^12)*10^12⌋ := by
  have hn : z.natAbs ≤ 9180000000 := by
    change |z| ≤ 9180000000 at hz
    exact_mod_cast (Int.natCast_natAbs z ▸ hz : (z.natAbs:ℤ) ≤ 9180000000)
  have e : ((z.natAbs:ℕ):ℝ) = |(z:ℝ)| := by
    rw [←Int.cast_abs,←Int.natCast_natAbs,Int.cast_natCast]
  have even : W.left (|(z:ℝ)|/10^12) = W.left ((z:ℝ)/10^12) := by
    rcases le_total 0 (z:ℝ) with a | a
    · rw [abs_of_nonneg a]
    · rw [abs_of_nonpos a,neg_div,W.left_even]
  have h := width_floor_nat W p z.natAbs hn
  rw [e,even] at h
  exact h

end
end HadwigerNelson.Certificate.Hole

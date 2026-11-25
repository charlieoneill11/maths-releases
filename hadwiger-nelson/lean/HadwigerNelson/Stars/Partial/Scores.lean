import HadwigerNelson.Stars.Partial.RangeSound

namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (quant)
noncomputable section

def amp (r : Row) (k : Nat) : ℝ := (r.spectrum[k]?.getD 0 : Int)

def signedSum (k : Nat) (t : ℝ) : ℝ := ∑ i : Fin 132621,
  let r := sourceRow i.val
  (r.area:ℝ)*max 0 ((r.mean:ℝ)+amp r k*t)

def nativeSum (d : Nat) : ℝ := ∑ j : Fin 4122,
  let r := sourceRow (132621+j.val)
  (r.area:ℝ)*max 0 ((r.mean:ℝ)*d-quant)

theorem source_area (L : Layout.Physical) {i : Nat} (hi : i<136743) : 0 ≤ (sourceRow i).area := by
  change 0 ≤ ((source i).xhi-(source i).xlo)*((source i).yhi-(source i).ylo)
  obtain ⟨x,y⟩ := L.widths ⟨i,hi⟩
  exact mul_nonneg (sub_nonneg.mpr x.le) (sub_nonneg.mpr y.le)

theorem amp_nonneg (i k : Nat) : 0≤amp (sourceRow i) k := by
  have norm0 (v : Int) : 0 ≤ normalized (max 0 v) := by
    unfold normalized
    rw [if_neg (not_lt_of_ge (le_max_left 0 v))]
    exact Int.ediv_nonneg (mul_nonneg (mul_nonneg (le_max_left ..) (by decide)) (by decide)) (by decide)
  have h (ts : Array PairMoments) (j : Nat) : 0 ≤ magnitude ts j := norm0 _
  unfold amp sourceRow row
  split
  · simp
  · simp only [Array.getElem?_ofFn]
    split
    · simp only [Option.getD_some]
      exact_mod_cast h _ _
    · simp

theorem signedSum_mono (L : Layout.Physical) (k : Nat) : Monotone (signedSum k) := by
  intro u v h
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (max_le_max_left 0 (add_le_add_right
    (mul_le_mul_of_nonneg_left h (amp_nonneg i.val k)) _))
    (by exact_mod_cast source_area L (by omega : i.val<136743))

theorem signed_from_shards (pass : ∀ p:Fin 4,checkShard p.val=true) (j : Fin Data.count) :
    let q := Data.query j.val
    (total q:ℝ) ≤ (10000:ℝ)*signedSum q.harmonic ((q.threshold:ℝ)/10000) := by
  let q := Data.query j.val
  have S := all_shards_sound pass j
  have C : (total q:ℝ) ≤ ∑ i : Fin 132621, ((rowLine (sourceRow i.val) q:Int):ℝ) := by
    exact_mod_cast S
  apply C.trans_eq
  rw [signedSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let r := sourceRow i.val
  change ((rowLine r q:Int):ℝ) = 10000*((r.area:ℝ)*max 0 ((r.mean:ℝ)+amp r q.harmonic*((q.threshold:ℝ)/10000)))
  simp only [rowLine,Int.cast_mul,Int.cast_max,Int.cast_add,Int.cast_zero,Int.cast_natCast,Int.cast_ofNat]
  have scaleMax (m a t : ℝ) : max 0 (m*10000+a*t) = 10000*max 0 (m+a*(t/10000)) := by
    rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ)≤10000),mul_zero]
    congr 1
    ring
  dsimp only [amp]
  rw [scaleMax]
  ring

theorem native_from_shards (pass : checkShard 3=true) (d : Nat) (hd : 0<d) (cap : d≤89) :
    (Data.native d:ℝ) ≤ nativeSum d := by
  have S := native_shard_sound pass d hd cap
  rw [←Fin.sum_univ_eq_sum_range] at S
  have casted := (Int.cast_le (R:=ℝ)).mpr S
  simpa only [Int.cast_sum,rowNative,Int.cast_mul,Int.cast_max,Int.cast_zero,Int.cast_sub,
    Int.cast_natCast,nativeSum] using casted

private theorem native_average_eq (d : Nat) (hd : 0<d) :
    nativeSum d/(d:ℝ) = ∑ j : Fin 4122,
      let r := sourceRow (132621+j.val)
      (r.area:ℝ)*max 0 ((r.mean:ℝ)-(quant:ℝ)/d) := by
  have pos : (0:ℝ)<d := by exact_mod_cast hd
  rw [nativeSum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_div_assoc,←max_div_div_right pos.le,zero_div,sub_div,mul_div_cancel_right₀ _ pos.ne']

theorem native_average_mono (L : Layout.Physical) (u v : Nat) (hu : 0<u) (uv : u≤v) :
    nativeSum u/(u:ℝ) ≤ nativeSum v/(v:ℝ) := by
  have pu : (0:ℝ)<u := by exact_mod_cast hu
  have rv : (u:ℝ)≤v := by exact_mod_cast uv
  rw [native_average_eq u hu,native_average_eq v (hu.trans_le uv)]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left (max_le_max_left 0 (sub_le_sub_left
    (div_le_div_of_nonneg_left (by norm_num [quant] : 0≤(quant:ℝ)) pu rv) _))
  exact_mod_cast source_area L (by omega : 132621+j.val<136743)

end
end HadwigerNelson.Stars.PartialCheck

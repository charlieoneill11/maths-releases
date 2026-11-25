import HadwigerNelson.Stars.Partial.Moments
import HadwigerNelson.Stars.AngularPhase
import HadwigerNelson.Arithmetic.ArcSums
import HadwigerNelson.Arithmetic.Angle
import HadwigerNelson.Arithmetic.Pi

namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (Arc Span resolution endpoint spanArc)
open Arithmetic

theorem arcPrefix_succ (n : Nat) :
    arcPrefix (n+1) =
    let p := arcPrefix n
    let e : Arc := ⟨p.1.low+(arcStep n).low,p.1.high+(arcStep n).high⟩
    (e,p.2.push e) := rfl

theorem arcPrefix_size (n : Nat) : (arcPrefix n).2.size = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [arcPrefix_succ,ih]

theorem arcPrefix_get (i n : Nat) (hi : i≤n) : (arcPrefix n).2[i]? = some (arcPrefix i).1 := by
  induction n with
  | zero =>
    obtain rfl : i=0 := by omega
    rfl
  | succ n ih =>
    rw [arcPrefix_succ]
    by_cases eq : i=n+1
    · subst i
      conv_lhs => rw [←arcPrefix_size n]
      rw [Array.getElem?_push_size,arcPrefix_succ]
    · have h : i<(arcPrefix n).2.size := by rw [arcPrefix_size];omega
      rw [Array.getElem?_push_lt h,←Array.getElem?_eq_getElem h]
      exact ih (by omega)

private theorem bin (i q : Nat) :
    ((arcStep i).low : ℝ) ≤ (scale:ℝ)*endpoint q (i+1)-(scale:ℝ)*endpoint q i ∧
    (scale:ℝ)*endpoint q (i+1)-(scale:ℝ)*endpoint q i ≤ (arcStep i).high := by
  let n : Int := resolution
  let j : Int := i
  let den := n*n+j*(j+1)
  have hn : 0<n := by decide
  have hj : 0≤j := by positivity
  have hd : 0<den := by dsimp [den];positivity
  have dn : (n:ℝ)*(n:ℝ) ≤ (den:ℝ) := by
    dsimp [den];push_cast
    have jnon : (0:ℝ) ≤ j := by exact_mod_cast hj
    nlinarith [sq_nonneg (j:ℝ)]
  have dn' : 0<(den:ℝ) := by exact_mod_cast hd
  have ratio : (n:ℝ)/(den:ℝ) ≤ 1/131072 := by
    apply (div_le_iff₀ dn').2
    change (131072:ℝ)*131072 ≤ (den:ℝ) at dn
    change 131072 ≤ (1:ℝ)/131072*(den:ℝ)
    linarith only [dn]
  have cube := pow_le_pow_left₀ (show (0:ℝ) ≤ (n:ℝ)/den by positivity) ratio 3
  have cubic : 2*(scale:ℝ)*((n:ℝ)/den)^3≤3 := by
    norm_num [scale] at cube ⊢
    linarith only [cube]
  have app := rounded_arctan_weight n den scale hn.le hd (by decide) cubic
  have id : (scale:ℝ)*endpoint q (i+1)-(scale:ℝ)*endpoint q i =
      2*(scale:ℝ)*Real.arctan ((n:ℝ)/den) := by
    have ar := arctan_bin_eq n j hn hj
    change Real.arctan (((i:ℝ)+1)/resolution)-Real.arctan ((i:ℝ)/resolution) = _ at ar
    unfold endpoint BoxCheck.paramAngle
    have realden : (den:ℝ) = (n:ℝ)^2+(j:ℝ)*(j+1) := by dsimp [den];push_cast;ring
    rw [realden,←ar]
    push_cast;ring
  rw [id]
  simpa only [arcStep,Int.cast_sub,Int.cast_one] using app

theorem spanArc_bounds (p : Span) (ab : p.start≤p.stop) (hb : p.stop≤resolution) :
    ((spanArc arcTable p).low:ℝ) ≤ scale*(endpoint p.quadrant p.stop-endpoint p.quadrant p.start) ∧
    scale*(endpoint p.quadrant p.stop-endpoint p.quadrant p.start) ≤ (spanArc arcTable p).high := by
  have h := arc_prefix_bounds (fun i => (arcPrefix i).1.low) (fun i => (arcPrefix i).1.high)
    (fun i => (scale:ℝ)*endpoint p.quadrant i) ab (fun i _ _ => by
      simpa only [arcPrefix_succ,add_sub_cancel_left] using bin i p.quadrant)
  simpa only [mul_sub,spanArc,arcTable,arcPrefix_get _ _ (ab.trans hb),arcPrefix_get _ _ hb,Option.getD_some] using h

theorem normalized_le (v : Int) : (normalized v:ℝ)/BoxCheck.quant ≤ (v:ℝ)/(2*scale*Real.pi) := by
  have p := moment_scaled_le v scale BoxCheck.quant (by decide) (by decide)
  have eq : signedScale v BoxCheck.quant (2*scale*31415926) (2*scale*31415927) 10000000 =
      normalized v := by by_cases neg : v<0 <;> simp [normalized,signedScale,neg]
  rw [eq] at p
  apply (div_le_iff₀ (by norm_num [BoxCheck.quant] : (0:ℝ)<BoxCheck.quant)).2
  convert p using 1 <;> ring

end HadwigerNelson.Stars.PartialCheck

import HadwigerNelson.Stars.Partial.Strip
import HadwigerNelson.Stars.WaveClassifier

namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (Status code merge scanRows)

noncomputable section

def columnX (colour : Nat) (m : Int) (x : ℝ) : ℝ :=
  if colour ≤ 3 then x-m*(2*PartialWave.xInt) else m*(2*PartialWave.xInt)-x

def columnY (m : Int) (y : ℝ) : ℝ := y-750000000000*m

def HasRow (c : Nat) (x y : ℝ) : Prop := ∃ j : Int, code c j = c ∧ InBand j x y

def HasCode (c : Nat) (x y : ℝ) : Prop := ∃ m : Int, HasRow c (columnX c m x) (columnY m y)

private theorem local_width {c : Nat} {x y : ℝ} (p : HasRow c x y) : 0 < x ∧ x < 10^12 := by
  obtain ⟨j,_,_,_,l,r⟩ := p
  have low := (PartialWave.datum.left_bounds ((y-j*500000000000)/10^12)).1
  have high := (PartialWave.datum.right_bounds ((y-j*500000000000)/10^12)).2
  unfold scaled at l r
  constructor <;> linarith

private theorem rows_sound (lo hi low high : Int) (c : Nat) (x y : ℝ)
    (xl : lo < x) (xr : x < hi) (yl : low < y) (yr : y < high) :
    let a := low / 500000000000
    let b := high / 500000000000
    let F (i : Nat) := if code c (a+i) == c then strip lo hi low high (a+i) else Status.outside
    (scanRows F (b-a+1).toNat = .inside → HasRow c x y) ∧
    (scanRows F (b-a+1).toNat = .outside → ¬HasRow c x y) := by
  dsimp only
  rw [BoxCheck.scanRows_inside,BoxCheck.scanRows_outside]
  constructor
  · rintro ⟨i,_,hi⟩
    split at hi
    · rename_i eq
      exact ⟨_,beq_iff_eq.mp eq,(strip_sound _ _ _ _ _ _ _ xl xr yl yr).1 hi⟩
    · cases hi
  · rintro out ⟨j,key,band⟩
    let a := low/500000000000
    let b := high/500000000000
    have lo' : a ≤ j := by
      apply (Int.ediv_le_iff_le_mul (by decide : (0:Int)<500000000000)).2
      exact_mod_cast (by linarith only [yl,band.2.1] : (low:ℝ)<j*500000000000+500000000000)
    have hi' : j ≤ b := by
      by_contra! bad
      have r := Int.lt_mul_of_ediv_lt (by decide : (0:Int)<500000000000) bad
      have t : (high:ℝ)<j*500000000000 := by exact_mod_cast r
      linarith only [band.1,yr,t]
    let i := (j-a).toNat
    have eq : a+(i:Int)=j := by dsimp [i]; omega
    have inside : i<(b-a+1).toNat := by dsimp [i]; omega
    have fail := out i inside
    change (if code c (a+(i:Int)) == c then strip lo hi low high (a+i) else .outside) = .outside at fail
    simp only [eq,key,beq_self_eq_true,if_true] at fail
    exact (strip_sound lo hi low high j x y xl xr yl yr).2 fail band

theorem column_sound (box : Angular.Box) (c : Nat) (m : Int) (x y : ℝ)
    (hz : BoxCheck.InBox box x y) :
    (column box c m = .inside → HasRow c (columnX c m x) (columnY m y)) ∧
    (column box c m = .outside → ¬HasRow c (columnX c m x) (columnY m y)) := by
  let u : Int := 2*PartialWave.xInt
  let lo := if c ≤ 3 then box.xlo-m*u else m*u-box.xhi
  let hi := if c ≤ 3 then box.xhi-m*u else m*u-box.xlo
  let low := box.ylo-750000000000*m
  let high := box.yhi-750000000000*m
  obtain ⟨xl,xr,yl,yr⟩ := hz
  have hxl : (lo:ℝ)<columnX c m x := by by_cases side : c≤3 <;> simp [lo,columnX,u,side] <;> linarith
  have hxr : columnX c m x<(hi:ℝ) := by by_cases side : c≤3 <;> simp [hi,columnX,u,side] <;> linarith
  have hyl : (low:ℝ)<columnY m y := by simpa [columnY,low] using yl
  have hyr : columnY m y<(high:ℝ) := by simpa [columnY,high] using yr
  let first := low/500000000000
  let rows := scanRows (fun i => if code c (first+i) == c then strip lo hi low high (first+i) else .outside)
    (high/500000000000-first+1).toNat
  have h : column box c m = if hi<0 ∨ 1000000000000<lo then .outside else rows := by
    by_cases side : c≤3 <;> simp [column,low,high,rows,first,lo,hi,u,side]
  rw [h]
  split
  · rename_i sep
    simp only [reduceCtorEq,false_implies,true_implies,true_and]
    intro row
    obtain ⟨hx0,hx1⟩ := local_width row
    cases sep with
    | inl p =>
      have t : (hi:ℝ)<0 := by exact_mod_cast p
      linarith only [t,hxr,hx0]
    | inr p =>
      have t : (1000000000000:ℝ)<lo := by exact_mod_cast p
      linarith only [t,hxl,hx1]
  · exact rows_sound lo hi low high c _ _ hxl hxr hyl hyr

theorem classify_sound (box : Angular.Box) (c : Nat) (x y : ℝ)
    (hz : BoxCheck.InBox box x y) (win : -(2*10^12) ≤ x ∧ x ≤ 2*10^12) :
    (classify box c = .inside → HasCode c x y) ∧
    (classify box c = .outside → ¬HasCode c x y) := by
  simp only [classify,BoxCheck.merge_inside,BoxCheck.merge_outside]
  constructor
  · rintro ((h|h)|h) <;> exact ⟨_,(column_sound box c _ _ _ hz).1 h⟩
  · rintro ⟨⟨l,o⟩,r⟩ ⟨m,p⟩
    have hx := local_width p
    have positions : m = -1 ∨ m = 0 ∨ m = 1 := by
      by_contra! h
      have out : m ≤ -2 ∨ 2 ≤ m := by omega
      obtain ⟨lx,rx⟩ := hx
      obtain ⟨w0,w1⟩ := win
      cases out with
      | inl h =>
        have h' : (m:ℝ) ≤ -2 := by exact_mod_cast h
        by_cases hc : c≤3 <;> simp [columnX,PartialWave.xInt,hc] at lx rx <;> linarith
      | inr h =>
        have h' : (2:ℝ) ≤ m := by exact_mod_cast h
        by_cases hc : c≤3 <;> simp [columnX,PartialWave.xInt,hc] at lx rx <;> linarith
    rcases positions with rfl|rfl|rfl
    · exact (column_sound box c _ _ _ hz).2 l p
    · exact (column_sound box c _ _ _ hz).2 o p
    · exact (column_sound box c _ _ _ hz).2 r p

end
end HadwigerNelson.Stars.PartialCheck

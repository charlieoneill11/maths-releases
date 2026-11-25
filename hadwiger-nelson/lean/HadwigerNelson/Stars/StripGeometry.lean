import HadwigerNelson.Stars.BoxRuntime
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Sound classification of an open rectangular destination against a
single translated band of the complete wave. -/

namespace HadwigerNelson.Stars.BoxCheck
open CompleteWave (height)
open Set

/-- The exact right wall, measured in units of 10⁻¹², is unimodal on one band.
The two interpolation witnesses bound the exact ordinate at integer heights. -/
structure WallBounds (f : ℝ → ℝ) : Prop where
  low : ∀ j : Int, 0 ≤ j → j ≤ height → (wall j).1 ≤ f j
  high : ∀ j : Int, 0 ≤ j → j ≤ height → f j ≤ (wall j).2
  rising : MonotoneOn f (Icc 0 ((height : ℝ)/2))
  falling : AntitoneOn f (Icc ((height : ℝ)/2) (height : ℝ))
  maximum : f ((height : ℝ)/2) ≤ peak

private theorem half_height : ((height : Int)/2 : Int) = 250000000000 := by decide
private theorem real_half_height : (height : ℝ)/2 = 250000000000 := by
  norm_num [CompleteWave.height,CompleteWave.scale]

theorem wall_interval_lower {f : ℝ → ℝ} (h : WallBounds f) {a b : Int} {y : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ height) (hay : a ≤ y) (hyb : y ≤ b) :
    ((min (wall a).1 (wall b).1 : Int) : ℝ) ≤ f y := by
  have hab : a ≤ b := by exact_mod_cast hay.trans hyb
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (b : ℝ) ≤ height := by exact_mod_cast hb
  by_cases below : y ≤ (height : ℝ)/2
  · exact (Int.cast_le.mpr (min_le_left ..)).trans ((h.low a ha (hab.trans hb)).trans
      (h.rising ⟨ha',hay.trans below⟩ ⟨ha'.trans hay,below⟩ hay))
  · have above := le_of_not_ge below
    exact (Int.cast_le.mpr (min_le_right ..)).trans ((h.low b (ha.trans hab) hb).trans
      (h.falling ⟨above,hyb.trans hb'⟩ ⟨above.trans hyb,hb'⟩ hyb))

theorem wall_interval_upper {f : ℝ → ℝ} (h : WallBounds f) {a b : Int} {y : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ height) (hay : a ≤ y) (hyb : y ≤ b) :
    f y ≤ ((if a ≤ (height : Int)/2 && (height : Int)/2 ≤ b then peak
              else max (wall a).2 (wall b).2 : Int) : ℝ) := by
  have hab : a ≤ b := by exact_mod_cast hay.trans hyb
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (b : ℝ) ≤ height := by exact_mod_cast hb
  have hz : 0 ≤ (height : ℝ)/2 := by rw [real_half_height]; norm_num
  have hhalf : (height : ℝ)/2 ≤ height := by linarith
  have yr := ha'.trans hay
  have ys := hyb.trans hb'
  by_cases side : a ≤ (height : Int)/2 ∧ (height : Int)/2 ≤ b
  · simp only [Bool.and_eq_true, decide_eq_true_eq, side, and_self, if_true]
    by_cases l : y ≤ (height : ℝ)/2
    · exact (h.rising ⟨yr,l⟩ ⟨hz,le_rfl⟩ l).trans h.maximum
    · exact (h.falling ⟨le_rfl,hhalf⟩ ⟨le_of_not_ge l,ys⟩ (le_of_not_ge l)).trans h.maximum
  · simp only [Bool.and_eq_true, decide_eq_true_eq, side, if_false]
    by_cases left : b < (height : Int)/2
    · rw [half_height] at left
      have bb : (b : ℝ) ≤ (height : ℝ)/2 := by rw [real_half_height]; exact_mod_cast left.le
      exact ((h.rising ⟨yr,hyb.trans bb⟩ ⟨ha'.trans (hay.trans hyb),bb⟩ hyb).trans
        (h.high b (ha.trans hab) hb)).trans (Int.cast_le.mpr (le_max_right ..))
    · have above : (height : Int)/2 < a := lt_of_not_ge (fun h => side ⟨h,le_of_not_gt left⟩)
      rw [half_height] at above
      have aa : (height : ℝ)/2 ≤ a := by rw [real_half_height]; exact_mod_cast above.le
      exact ((h.falling ⟨aa,hay.trans ys⟩ ⟨aa.trans hay,ys⟩ hay).trans
        (h.high a ha (hab.trans hb))).trans (Int.cast_le.mpr (le_max_left ..))

/-- Membership in the translated strip, using the scaled height and the
unreflected local horizontal coordinate. -/
def InStrip (f : ℝ → ℝ) (j : Int) (x y : ℝ) : Prop :=
  (j : ℝ)*height < y ∧ y < ((j : ℝ)+1)*height ∧ 0 < x ∧ x < f (y-j*height)

/-- Intersecting the vertical range of a destination with the band retains
any interior point of both rectangles. -/
private theorem clamp_band {low high j : Int} {y : ℝ} (yl : low < y) (yr : y < high)
    (lowBand : (j : ℝ)*height < y) (highBand : y < ((j : ℝ)+1)*height) :
    let h : Int := height
    let a := min h (max 0 (low-j*h))
    let b := min h (max 0 (high-j*h))
    0 ≤ a ∧ b ≤ h ∧ (a : ℝ) < y-j*height ∧ y-j*height < b := by
  dsimp only
  have hpos : (0 : ℝ) < height := by norm_num [CompleteWave.height,CompleteWave.scale]
  have hr : y-(j : ℝ)*height < height := by linarith only [highBand]
  have hl : 0 < y-(j : ℝ)*height := by linarith only [lowBand]
  refine ⟨le_min (by exact_mod_cast hpos.le) (le_max_left ..), min_le_left .., ?_, ?_⟩
  · push_cast
    apply lt_of_le_of_lt (min_le_right ..)
    exact max_lt hl (by linarith only [yl])
  · push_cast
    apply lt_min hr
    apply lt_of_lt_of_le _ (le_max_right ..)
    linarith only [yr]

/-- The inside/outside statuses enclose the open destination rectangle
against the exact colour strip. -/
theorem strip_sound {f : ℝ → ℝ} (hw : WallBounds f) (lo hi low high j : Int)
    (x y : ℝ) (xl : lo < x) (xr : x < hi) (yl : low < y) (yr : y < high) :
    (strip lo hi low high j = .inside → InStrip f j x y) ∧
    (strip lo hi low high j = .outside → ¬ InStrip f j x y) := by
  let h : Int := height
  let a := min h (max 0 (low-j*h))
  let b := min h (max 0 (high-j*h))
  change
    ((if b ≤ a then .outside else
      if j*h ≤ low && high ≤ (j+1)*h && 0 ≤ lo && hi ≤ min (wall a).1 (wall b).1 then .inside else
      if lo < (if a ≤ h/2 && h/2 ≤ b then peak else max (wall a).2 (wall b).2)
        then .uncertain else .outside : Status) = .inside → _) ∧
    ((if b ≤ a then .outside else
      if j*h ≤ low && high ≤ (j+1)*h && 0 ≤ lo && hi ≤ min (wall a).1 (wall b).1 then .inside else
      if lo < (if a ≤ h/2 && h/2 ≤ b then peak else max (wall a).2 (wall b).2)
        then .uncertain else .outside : Status) = .outside → _)
  by_cases disjoint : b ≤ a
  · simp only [if_pos disjoint, reduceCtorEq, false_implies, true_implies, true_and]
    rintro ⟨y0,y1,-,-⟩
    obtain ⟨_,_,ha,hb⟩ := clamp_band yl yr y0 y1
    have r : (b : ℝ) ≤ a := by exact_mod_cast disjoint
    exact (not_lt_of_ge r) (ha.trans hb)
  simp only [if_neg disjoint, Bool.and_eq_true, decide_eq_true_eq]
  by_cases ins : ((j*h ≤ low ∧ high ≤ (j+1)*h) ∧ 0 ≤ lo) ∧ hi ≤ min (wall a).1 (wall b).1
  · simp only [if_pos ins, true_implies, reduceCtorEq, false_implies, and_true]
    obtain ⟨⟨⟨hl,hr⟩,hx⟩,hwid⟩ := ins
    have y0 : (j : ℝ)*height < y := lt_of_le_of_lt (by exact_mod_cast hl) yl
    have y1 : y < ((j : ℝ)+1)*height := lt_of_lt_of_le yr (by exact_mod_cast hr)
    obtain ⟨za,bh,ya,yb⟩ := clamp_band yl yr y0 y1
    exact ⟨y0,y1,lt_of_le_of_lt (by exact_mod_cast hx) xl,
      xr.trans_le ((Int.cast_le.mpr hwid).trans (wall_interval_lower hw za bh ya.le yb.le))⟩
  simp only [if_neg ins]
  by_cases poss : lo < (if a ≤ h/2 ∧ h/2 ≤ b then peak else max (wall a).2 (wall b).2)
  · simp [poss]
  simp only [if_neg poss, reduceCtorEq, false_implies, true_implies, true_and]
  rintro ⟨y0,y1,_,xmem⟩
  obtain ⟨za,bh,ya,yb⟩ := clamp_band yl yr y0 y1
  have up := wall_interval_upper hw za bh ya.le yb.le
  simp only [Bool.and_eq_true, decide_eq_true_eq] at up
  have htop := Int.cast_le (R := ℝ) |>.mpr (le_of_not_gt poss)
  exact (not_lt_of_ge ((up.trans htop).trans xl.le)) xmem

@[simp] theorem merge_outside (a b : Status) : merge a b = .outside ↔ a = .outside ∧ b = .outside := by
  cases a <;> cases b <;> decide

@[simp] theorem merge_inside (a b : Status) : merge a b = .inside ↔ a = .inside ∨ b = .inside := by
  cases a <;> cases b <;> decide

theorem scanRows_inside (f : Nat → Status) (n : Nat) :
    scanRows f n = .inside ↔ ∃ i < n, f i = .inside := by
  induction n with
  | zero => simp [scanRows]
  | succ n ih =>
    rw [scanRows,merge_inside,ih]
    constructor
    · rintro (⟨i,hi,hf⟩|hf)
      · exact ⟨i,Nat.lt_succ_of_lt hi,hf⟩
      · exact ⟨n,Nat.lt_succ_self _,hf⟩
    · rintro ⟨i,hi,hf⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h|rfl
      · exact Or.inl ⟨_,h,hf⟩
      · exact Or.inr hf

theorem scanRows_outside (f : Nat → Status) (n : Nat) :
    scanRows f n = .outside ↔ ∀ i < n, f i = .outside := by
  induction n with
  | zero => simp [scanRows]
  | succ n ih =>
    rw [scanRows,merge_outside,ih]
    constructor
    · rintro ⟨h,hf⟩ i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with ht|rfl
      · exact h i ht
      · exact hf
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi),h n (Nat.lt_succ_self _)⟩

def HasRow (f : ℝ → ℝ) (c : Nat) (x y : ℝ) : Prop :=
  ∃ j : Int, code c j = c ∧ InStrip f j x y

/-- The finitely scanned row interval contains exactly the possible strips. -/
theorem checkRows_sound {f : ℝ → ℝ} (hw : WallBounds f) (lo hi low high : Int)
    (c : Nat) (x y : ℝ) (xl : lo < x) (xr : x < hi) (yl : low < y) (yr : y < high) :
    (checkRows lo hi low high c = .inside → HasRow f c x y) ∧
    (checkRows lo hi low high c = .outside → ¬ HasRow f c x y) := by
  let h : Int := height
  let a := low/h
  let b := high/h
  let test (i : Nat) := if code c (a+i) == c then strip lo hi low high (a+i) else .outside
  change (scanRows test (b-a+1).toNat = .inside → _) ∧ (scanRows test (b-a+1).toNat = .outside → _)
  rw [scanRows_inside,scanRows_outside]
  constructor
  · rintro ⟨i,_,hi⟩
    by_cases key : code c (a+i) = c
    · exact ⟨a+i,key,(strip_sound hw lo _ low high (a+i) x y xl xr yl yr).1 (by simpa [test,key] using hi)⟩
    · simp [test,key] at hi
  · rintro out ⟨j,hj,yst⟩
    have hp : 0 < h := by decide
    have jlo : a ≤ j := by
      apply (Int.ediv_le_iff_le_mul hp).2
      have r : (low : ℝ) < (j : ℝ)*height+height := by linarith only [yl,yst.2.1]
      exact_mod_cast r
    have jhi : j ≤ b := by
      by_contra! hn
      have t := Int.lt_mul_of_ediv_lt hp hn
      have r : (high : ℝ) < (j : ℝ)*height := by exact_mod_cast t
      linarith only [yst.1,yr,r]
    let i := (j-a).toNat
    have id : a+(i : Int) = j := by dsimp [i]; omega
    have within : i < (b-a+1).toNat := by dsimp [i]; omega
    have fail := out i within
    simp only [test,id,hj,beq_self_eq_true,if_true] at fail
    exact (strip_sound hw lo hi low high j x y xl xr yl yr).2 fail yst

/-- Maximal width throughout the translated open strip. -/
theorem row_width {f : ℝ → ℝ} (hw : WallBounds f) {c : Nat} {x y : ℝ}
    (row : HasRow f c x y) : 0 < x ∧ x < peak := by
  obtain ⟨j,_,y0,y1,hx,xf⟩ := row
  have hl : 0 ≤ y-j*height := by linarith only [y0]
  have hr : y-j*height ≤ height := by linarith only [y1]
  have hhalf : 0 ≤ (height : ℝ)/2 ∧ (height : ℝ)/2 ≤ height := by
    norm_num [CompleteWave.height,CompleteWave.scale]
  by_cases side : y-j*height ≤ (height : ℝ)/2
  · exact ⟨hx,xf.trans_le ((hw.rising ⟨hl,side⟩ ⟨hhalf.1,le_rfl⟩ side).trans hw.maximum)⟩
  · have above := le_of_not_ge side
    exact ⟨hx,xf.trans_le ((hw.falling ⟨le_rfl,hhalf.2⟩ ⟨above,hr⟩ above).trans hw.maximum)⟩

/-- Horizontal orientation relative to the centre m of a mirrored pair. -/
def columnX (c : Nat) (m : Int) (x : ℝ) : ℝ :=
  if c ≤ 3 then x-m*(2*CompleteWave.xInt) else m*(2*CompleteWave.xInt)-x

def columnY (m : Int) (y : ℝ) : ℝ := y - ((3*m*(height : Int)/2 : Int) : ℝ)

def InBox (b : Angular.Box) (x y : ℝ) : Prop :=
  b.xlo < x ∧ x < b.xhi ∧ b.ylo < y ∧ y < b.yhi

theorem column_sound {f : ℝ → ℝ} (hw : WallBounds f) (b : Angular.Box) (c : Nat) (m : Int)
    (x y : ℝ) (inside : InBox b x y) :
    (column b c m = .inside → HasRow f c (columnX c m x) (columnY m y)) ∧
    (column b c m = .outside → ¬ HasRow f c (columnX c m x) (columnY m y)) := by
  obtain ⟨xl,xr,yl,yr⟩ := inside
  let u : Int := 2*CompleteWave.xInt
  let h : Int := height
  let lo := if c ≤ 3 then b.xlo-m*u else m*u-b.xhi
  let hi := if c ≤ 3 then b.xhi-m*u else m*u-b.xlo
  have lx : (lo : ℝ) < columnX c m x := by
    by_cases hc : c ≤ 3 <;> simp [lo,u,columnX,hc] <;> linarith
  have rx : columnX c m x < (hi : ℝ) := by
    by_cases hc : c ≤ 3 <;> simp [hi,u,columnX,hc] <;> linarith
  have ly : ((b.ylo-3*m*h/2 : Int) : ℝ) < columnY m y := by
    simpa [columnY,h] using yl
  have ry : columnY m y < ((b.yhi-3*m*h/2 : Int) : ℝ) := by
    simpa [columnY,h] using yr
  have unfold_column : column b c m =
      if hi ≤ 0 || peak ≤ lo then .outside else checkRows lo hi (b.ylo-3*m*h/2) (b.yhi-3*m*h/2) c := by
    by_cases hc : c ≤ 3 <;> simp [column,lo,hi,h,u,hc]
  rw [unfold_column]
  simp only [Bool.or_eq_true,decide_eq_true_eq]
  by_cases empty : hi ≤ 0 ∨ peak ≤ lo
  · simp only [if_pos empty, reduceCtorEq, false_implies, true_implies,true_and]
    intro row
    have ⟨r0,r1⟩ := row_width hw row
    rcases empty with h|h
    · have : (hi : ℝ) ≤ 0 := by exact_mod_cast h
      linarith
    · have : (peak : ℝ) ≤ (lo : ℝ) := by exact_mod_cast h
      linarith
  · simpa only [if_neg empty] using checkRows_sound hw lo hi _ _ c _ _ lx rx ly ry

/-- The release's finite five-column union exactly controls interior points
in the destination range covered by the source rectangles and unit rays. -/
def HasCode (f : ℝ → ℝ) (c : Nat) (x y : ℝ) : Prop :=
  ∃ m : Int, HasRow f c (columnX c m x) (columnY m y)

theorem classify_sound {f : ℝ → ℝ} (hw : WallBounds f) (b : Angular.Box) (c : Nat)
    (x y : ℝ) (inside : InBox b x y)
    (window : -(2*(CompleteWave.scale : ℝ)) ≤ x ∧ x ≤ 2*(CompleteWave.scale : ℝ))
    (gap : (2*(CompleteWave.scale : ℝ)) < 3*(2*(CompleteWave.xInt : ℝ))-peak) :
    (classify b c = .inside → HasCode f c x y) ∧
    (classify b c = .outside → ¬ HasCode f c x y) := by
  simp only [classify,merge_inside,merge_outside]
  constructor
  · rintro (((hm|hm)|hm)|(hm|hm)) <;> exact ⟨_,(column_sound hw b c _ x y inside).1 hm⟩
  · rintro ⟨⟨⟨h₁,h₂⟩,h₃⟩,h₄,h₅⟩ ⟨m,row⟩
    have bounded : -2 ≤ m ∧ m ≤ 2 := by
      have ⟨r0,r1⟩ := row_width hw row
      simp only [columnX] at r0 r1
      obtain ⟨w0,w1⟩ := window
      have pos : (0 : ℝ) ≤ 2*CompleteWave.xInt := by norm_num [CompleteWave.xInt]
      by_contra! hout
      by_cases left : m < -2
      · have hm : (m : ℝ) ≤ -3 := by exact_mod_cast (by omega : m ≤ -3)
        have prod := mul_le_mul_of_nonneg_right hm pos
        by_cases hc : c ≤ 3 <;> simp only [hc,if_true,if_false] at r0 r1 <;> linarith
      · have hm : 3 ≤ (m : ℝ) := by exact_mod_cast (by omega : 3 ≤ m)
        have prod := mul_le_mul_of_nonneg_right hm pos
        by_cases hc : c ≤ 3 <;> simp only [hc,if_true,if_false] at r0 r1 <;> linarith
    have possible : m = -2 ∨ m = -1 ∨ m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases possible with rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact (column_sound hw b c _ x y inside).2 h₁ row
      | exact (column_sound hw b c _ x y inside).2 h₂ row
      | exact (column_sound hw b c _ x y inside).2 h₃ row
      | exact (column_sound hw b c _ x y inside).2 h₄ row
      | exact (column_sound hw b c _ x y inside).2 h₅ row

end HadwigerNelson.Stars.BoxCheck

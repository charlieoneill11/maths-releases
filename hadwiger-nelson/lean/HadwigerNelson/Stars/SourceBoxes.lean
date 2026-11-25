import HadwigerNelson.Stars.CreditSound
import HadwigerNelson.Stars.Envelope
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto

/-! A linear-size certificate that all harmonic boxes lie in the lower half
of the master tile and have pairwise disjoint interiors. Integer coordinates
in this file, except in Source.box, use millionths. -/

namespace HadwigerNelson.Stars.BoxCheck

def zone (i : Nat) : Nat :=
  if i < 1200 then 0 else if i < 2384 then 1 else if i < 4464 then 2 else 3

def zoneLeft : Nat → Int
  | 0 => 0 | 1 => 80 | 2 => 866000 | _ => 876400

def zoneRight : Nat → Int
  | 0 => 65 | 1 => 6000 | 2 => 876400 | _ => 1000000

def majorY (z : Nat) : Bool := z == 0 || z == 3

def slabWidth (z : Nat) : Int := if z == 3 then 100 else 20

def slabOffset : Nat → Int
  | 0 => 0 | 1 => -5920 | 2 => 854080 | _ => -111600

def lowerMajor (s : Source) (z : Nat) := if majorY z then s.ylo else s.xlo
def upperMajor (s : Source) (z : Nat) := if majorY z then s.yhi else s.xhi

def disjointBox (a b : Source) : Bool :=
  a.xhi ≤ b.xlo || b.xhi ≤ a.xlo || a.yhi ≤ b.ylo || b.yhi ≤ a.ylo

def sourceValid (i : Nat) : Bool :=
  let s := source i
  let z := zone i
  let low := slabOffset z + slabWidth z*(i/4 : Nat)
  s.xlo < s.xhi && s.ylo < s.yhi && 0 ≤ s.ylo && s.yhi ≤ 250000 &&
    zoneLeft z ≤ s.xlo && s.xhi ≤ zoneRight z &&
    low ≤ lowerMajor s z && upperMajor s z ≤ low+slabWidth z &&
    (classify s.box 1 == .inside) &&
    (Array.ofFn fun k : Fin 4 => k.val == i%4 || disjointBox s (source (4*(i/4)+k.val))).all id

def saturatedValid (i : Nat) : Bool := classify (saturated i).box 1 == .inside

def checkSourceBoxes : Bool :=
  (Array.ofFn fun i : Fin 14464 => sourceValid i.val).all id &&
  (Array.ofFn fun i : Fin 252 => saturatedValid i.val).all id

def InSource (s : Source) (x y : ℝ) : Prop :=
  s.xlo < x ∧ x < s.xhi ∧ s.ylo < y ∧ y < s.yhi

theorem disjointBox_sound {a b : Source} (h : disjointBox a b = true)
    {x y : ℝ} (ha : InSource a x y) (hb : InSource b x y) : False := by
  simp only [disjointBox,Bool.or_eq_true,decide_eq_true_eq] at h
  rcases ha with ⟨h1,h2,h3,h4⟩
  rcases hb with ⟨h5,h6,h7,h8⟩
  rcases h with ((h|h)|h)|h
  · exact (not_lt_of_ge (Int.cast_le (R := ℝ) |>.mpr h)) (h5.trans h2)
  · exact (not_lt_of_ge (Int.cast_le (R := ℝ) |>.mpr h)) (h1.trans h6)
  · exact (not_lt_of_ge (Int.cast_le (R := ℝ) |>.mpr h)) (h7.trans h4)
  · exact (not_lt_of_ge (Int.cast_le (R := ℝ) |>.mpr h)) (h3.trans h8)

theorem sourceValid_spec {i : Nat} (h : sourceValid i = true) :
    let s := source i
    let z := zone i
    let low := slabOffset z + slabWidth z*(i/4 : Nat)
    s.xlo < s.xhi ∧ s.ylo < s.yhi ∧ 0 ≤ s.ylo ∧ s.yhi ≤ 250000 ∧
    zoneLeft z ≤ s.xlo ∧ s.xhi ≤ zoneRight z ∧
    low ≤ lowerMajor s z ∧ upperMajor s z ≤ low+slabWidth z ∧
    classify s.box 1 = .inside ∧
    ∀ k : Fin 4, k.val ≠ i%4 → disjointBox s (source (4*(i/4)+k.val)) = true := by
  dsimp only
  simp only [sourceValid,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨a,b⟩,c⟩,d⟩,e⟩,f⟩,g⟩,j⟩,cl⟩,all⟩
  refine ⟨a,b,c,d,e,f,g,j,cl,?_⟩
  intro k hk
  have h := Array.all_eq_true.mp all k.val (by simp)
  simpa [hk] using h

private theorem zones_separate {r t : Nat} (hr : r < 4) (ht : t < 4) (h : r < t) :
    zoneRight r ≤ zoneLeft t := by
  interval_cases r <;> interval_cases t <;> first | omega | decide

theorem first_zone (i : Nat) : zone i < 4 := by
  unfold zone
  split <;> first | decide | (split <;> first | decide | (split <;> decide))

theorem checked_disjoint {i j : Nat} (hi : sourceValid i = true)
    (hj : sourceValid j = true) (hij : i ≠ j)
    {x y : ℝ} (a : InSource (source i) x y) (b : InSource (source j) x y) : False := by
  obtain ⟨_,_,_,_,il,ir,i0,i1,_,same⟩ := sourceValid_spec hi
  obtain ⟨_,_,_,_,jl,jr,j0,j1,_,_⟩ := sourceValid_spec hj
  by_cases h : zone i = zone j
  · by_cases slab : i/4 = j/4
    · let k : Fin 4 := ⟨j%4,Nat.mod_lt _ (by decide)⟩
      have ne : k.val ≠ i%4 := by dsimp [k]; omega
      have dis := same k ne
      rw [show 4*(i/4)+k.val = j by dsimp [k]; omega] at dis
      exact disjointBox_sound dis a b
    · rw [← h] at j0 j1
      have w : 0 < slabWidth (zone i) := by unfold slabWidth; split <;> decide
      have choose (xx yy : Nat) (hn : xx < yy) :
          slabOffset (zone i)+slabWidth (zone i)*(xx : Int)+slabWidth (zone i) ≤
          slabOffset (zone i)+slabWidth (zone i)*(yy : Int) := by
        have h' : (xx : Int)+1 ≤ (yy : Int) := by omega
        have ht := Int.mul_le_mul_of_nonneg_left h' w.le
        linarith
      have ord : upperMajor (source i) (zone i) ≤ lowerMajor (source j) (zone i) ∨
          upperMajor (source j) (zone i) ≤ lowerMajor (source i) (zone i) := by
        rcases lt_or_gt_of_ne slab with h|h
        · exact Or.inl (i1.trans ((choose _ _ h).trans j0))
        · exact Or.inr (j1.trans ((choose _ _ h).trans i0))
      apply disjointBox_sound (a := source i) (b := source j) _ a b
      simp only [disjointBox,Bool.or_eq_true,decide_eq_true_eq]
      by_cases test : majorY (zone i) = true <;> simp [upperMajor,lowerMajor,test] at ord <;> tauto
  · apply disjointBox_sound (a := source i) (b := source j) _ a b
    simp only [disjointBox,Bool.or_eq_true,decide_eq_true_eq]
    rcases lt_or_gt_of_ne h with lt|gt
    · exact Or.inl (Or.inl (Or.inl (ir.trans ((zones_separate (first_zone _) (first_zone _) lt).trans jl))))
    · exact Or.inl (Or.inl (Or.inr (jr.trans ((zones_separate (first_zone _) (first_zone _) gt).trans il))))

theorem checkSourceBoxes_spec (pass : checkSourceBoxes = true) :
    (∀ i : Fin 14464, sourceValid i.val = true) ∧
    (∀ i : Fin 252, saturatedValid i.val = true) := by
  rw [checkSourceBoxes,Bool.and_eq_true] at pass
  exact ⟨(array_all_ofFn _).1 pass.1,(array_all_ofFn _).1 pass.2⟩

theorem source_valid_native {f : ℝ → ℝ} (hw : WallBounds f) {i : Fin 14464}
    (h : sourceValid i.val = true) {x y : ℝ} (inside : InBox (source i.val).box x y)
    (window : -(2*(CompleteWave.scale : ℝ)) ≤ x ∧ x ≤ 2*(CompleteWave.scale : ℝ))
    (gap : (2*(CompleteWave.scale : ℝ)) < 3*(2*(CompleteWave.xInt : ℝ))-peak) :
    HasCode f 1 x y :=
  (classify_sound hw _ 1 x y inside window gap).1 (sourceValid_spec h).2.2.2.2.2.2.2.2.1

theorem saturated_limits (i : Fin 252) :
    0 ≤ (saturated i.val).xlo ∧ (saturated i.val).xhi ≤ 600 ∧
    0 ≤ (saturated i.val).ylo ∧ (saturated i.val).yhi ≤ 1050 := by
  have := i.isLt
  dsimp [saturated]
  omega

theorem saturated_disjoint (i j : Fin 252) (different : i ≠ j) {x y : ℝ}
    (hi : InSource (saturated i.val) x y) (hj : InSource (saturated j.val) x y) : False := by
  apply disjointBox_sound _ hi hj
  have ne : i.val ≠ j.val := Fin.val_ne_of_ne different
  simp only [disjointBox,Bool.or_eq_true,decide_eq_true_eq,saturated]
  omega

theorem harmonic_separate_saturated {s : Source} (sep : s.separate = true) (i : Fin 252)
    {x y : ℝ} (src : InSource s x y) (sat : InSource (saturated i.val) x y) : False := by
  apply disjointBox_sound _ src sat
  have ⟨_,hx,_,hy⟩ := saturated_limits i
  simp only [Source.separate,Bool.or_eq_true,decide_eq_true_eq] at sep
  simp only [disjointBox,Bool.or_eq_true,decide_eq_true_eq]
  rcases sep with h|h
  · exact Or.inl (Or.inl (Or.inr (hx.trans h)))
  · exact Or.inr (hy.trans h)

end HadwigerNelson.Stars.BoxCheck

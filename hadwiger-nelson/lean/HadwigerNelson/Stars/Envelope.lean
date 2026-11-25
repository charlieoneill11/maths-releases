import HadwigerNelson.Stars.StripGeometry

/-! The meaning of the three colour statuses and of each signed angular span.
The release's integer coefficient and radius are twice the signed midpoint and
radius in indicator units. -/

namespace HadwigerNelson.Stars.BoxCheck

def Represents (s : Status) (event : Bool) : Prop :=
  (s = .inside → event = true) ∧ (s = .outside → event = false)

def indicator (b : Bool) : Int := if b then 1 else 0

/-- A certified status pair encloses the actual native-minus-alternate
indicator, provided the two colour classes are disjoint. -/
theorem signedStep_sound (u v : Status) (n a : Bool)
    (hn : Represents u n) (ha : Represents v a) (disjoint : ¬(n = true ∧ a = true)) :
    let s := signedStep u v
    |2*(indicator n-indicator a)-s.1| ≤ s.2 := by
  revert hn ha disjoint
  cases u <;> cases v <;> cases n <;> cases a <;> unfold Represents <;> decide

theorem classify_represents {f : ℝ → ℝ} (hw : WallBounds f) (b : Angular.Box) (c : Nat)
    (x y : ℝ) (inside : InBox b x y)
    (window : -(2*(CompleteWave.scale : ℝ)) ≤ x ∧ x ≤ 2*(CompleteWave.scale : ℝ))
    (gap : (2*(CompleteWave.scale : ℝ)) < 3*(2*(CompleteWave.xInt : ℝ))-peak)
    [Decidable (HasCode f c x y)] :
    Represents (classify b c) (decide (HasCode f c x y)) := by
  obtain ⟨hi,ho⟩ := classify_sound hw b c x y inside window gap
  exact ⟨fun hs => decide_eq_true (hi hs),fun hs => decide_eq_false (ho hs)⟩

def ClosedBox (b : Angular.Box) (u v : ℝ) : Prop :=
  b.xlo ≤ u ∧ u ≤ b.xhi ∧ b.ylo ≤ v ∧ v ≤ b.yhi

theorem destination_contains {src ray : Angular.Box} {x y u v : ℝ}
    (hs : InBox src x y) (hr : ClosedBox ray u v) :
    InBox (destination src ray) (x+u) (y+v) := by
  obtain ⟨x0,x1,y0,y1⟩ := hs
  obtain ⟨u0,u1,v0,v1⟩ := hr
  simpa [InBox,destination] using
    And.intro (add_lt_add_of_lt_of_le x0 u0)
      ⟨add_lt_add_of_lt_of_le x1 u1,add_lt_add_of_lt_of_le y0 v0,add_lt_add_of_lt_of_le y1 v1⟩

end HadwigerNelson.Stars.BoxCheck

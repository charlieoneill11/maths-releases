import SevenCycleRuntime.TypeThree
import SevenCycle.Proof.Bitsets

/-! # The exact six-band join

The three transverse axes in physical order are A, B and C. The coordinates of
a transverse support are the anchor axis followed by its other two transverse
axes in physical order. An input domain contains all rows with the two required
anchor cuts. This join checks the twelve crossings between different transverse
axes. Rows on the same axis impose no crossing condition on each other. -/

namespace SevenCycle.TypeThree

def cutsOf (r : Bitsets.Cube) : CutRow :=
  ⟨Bitsets.cut r 0 0, Bitsets.cut r 0 3, Bitsets.cut r 1 0, Bitsets.cut r 1 3,
   Bitsets.cut r 2 0, Bitsets.cut r 2 3⟩

/-- All constraints in their physical coordinate order. The last two domains
are on one axis, so their witnesses can be chosen independently. -/
structure Crosses (a a' b b' c c' : CutRow) : Prop where
  ab00 : a.b0 = b.b0
  ab30 : a'.b0 = b.b3
  ab03 : a.b3 = b'.b0
  ab33 : a'.b3 = b'.b3
  ac00 : a.c0 = c.b0
  ac30 : a'.c0 = c.b3
  bc00 : b.c0 = c.c0
  bc30 : b'.c0 = c.c3
  ac03 : a.c3 = c'.b0
  ac33 : a'.c3 = c'.b3
  bc03 : b.c3 = c'.c0
  bc33 : b'.c3 = c'.c3

/-- The two leading cuts of each transverse band are the cuts dictated by
the anchor pair. The remaining cuts agree at all twelve transverse crossings. -/
structure Joined (s t a a' b b' c c' : CutRow) : Prop where
  A0 : a.a0 = s.a0 ∧ a.a3 = t.a0
  A3 : a'.a0 = s.a3 ∧ a'.a3 = t.a3
  B0 : b.a0 = s.b0 ∧ b.a3 = t.b0
  B3 : b'.a0 = s.b3 ∧ b'.a3 = t.b3
  C0 : c.a0 = s.c0 ∧ c.a3 = t.c0
  C3 : c'.a0 = s.c3 ∧ c'.a3 = t.c3
  cross : Crosses a a' b b' c c'

/-- Search interface after restricting the source to translations of atlas rows. -/
def NoJoined (sources all : Array CutRow) : Prop :=
  ∀ s ∈ sources, ∀ t ∈ all, ∀ a ∈ all, ∀ a' ∈ all, ∀ b ∈ all, ∀ b' ∈ all,
    ∀ c ∈ all, ∀ c' ∈ all, ¬ Joined s t a a' b b' c c'

theorem rejectJoin_sound {a0 a3 b0 b3 c0 c3 : Array CutRow}
    (h : rejectJoin a0 a3 b0 b3 c0 c3 = true) {a a' b b' c c' : CutRow}
    (ha : a ∈ a0) (ha' : a' ∈ a3) (hb : b ∈ b0) (hb' : b' ∈ b3)
    (hc : c ∈ c0) (hc' : c' ∈ c3) : ¬ Crosses a a' b b' c c' := by
  intro x
  unfold rejectJoin at h
  rw [Bool.not_eq_true', ← Bool.not_eq_true] at h
  apply h
  simp only [Array.any_eq_true', Bool.and_eq_true]
  refine ⟨a, ha, a', ha', b, hb, ?_, b', hb', ⟨?_, ⟨c, hc, ?_⟩⟩, ⟨c', hc', ?_⟩⟩
  · simp [fitsB, mid, x.ab00, x.ab30]
  · simp [fitsB, mid, x.ab03, x.ab33]
  · simp [fitsC, last, x.ac00, x.ac30, x.bc00, x.bc30]
  · simp [fitsC, last, x.ac03, x.ac33, x.bc03, x.bc33]

end SevenCycle.TypeThree

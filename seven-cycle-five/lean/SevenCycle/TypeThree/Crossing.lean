import SevenCycle.Proof.Model
import Mathlib.Data.Fin.VecNotation

/-! # A checked planar filter for the type-three search

Fix the bands on axis 0 at starts 0 and 3, and one transverse band on axis 1.
In the four ambient coordinates (h,t,y,z), its crossings with the two anchor
bands are subsets of the (y,z)-plane. This filter rejects a domain only when
each stored transverse candidate disagrees with a prescribed crossing. -/

namespace SevenCycle.TypeThree

abbrev Cube := Vector UInt64 7
abbrev Height := ZMod 7
abbrev Words := Finset (Proof.Tuple 4)

def height (b : Bool) : Height := if b then 3 else 0

/-- Erasing the first coordinate is a bitwise union of the two planes.
Limit the result to the 49 used bits, even for an input with nonzero padding. -/
def cutKey (r : Cube) (s : Height) : BitVec 49 :=
  ((r.get s ||| r.get (s + (1 : Height) : Height)).toBitVec).setWidth 49

def contains (r : Cube) (h y z : Height) : Prop :=
  (r.get h).toNat.testBit (7 * y.val + z.val) = true

private theorem cutKey_bit (r : Cube) (s y z : Height) :
    (cutKey r s).getLsbD (7 * y.val + z.val) = true ↔
      contains r s y z ∨ contains r (s+1) y z := by
  have hy : y.val < 7 := y.isLt
  have hz : z.val < 7 := z.isLt
  have hi : 7 * y.val + z.val < 49 := by omega
  rw [cutKey, BitVec.getLsbD_setWidth, UInt64.toBitVec_or, BitVec.getLsbD_or]
  simp only [hi, decide_true, Bool.true_and, Bool.or_eq_true, contains]
  rfl

/-- The stored three-dimensional support is exactly the projection of the
specified band on the first ambient axis. -/
def Anchor (C : Words) (h : Height) (r : Cube) : Prop :=
  ∀ t y z, contains r t y z ↔ ![h,t,y,z] ∈ C ∨ ![h+1,t,y,z] ∈ C

def Transverse (C : Words) (t : Height) (r : Cube) : Prop :=
  ∀ h y z, contains r h y z ↔ ![h,t,y,z] ∈ C ∨ ![h,t+1,y,z] ∈ C

/-- The two stored masks describe the same four-dimensional crossing. -/
theorem crossing_eq {C : Words} {h t : Height} {r w : Cube}
    (hr : Anchor C h r) (hw : Transverse C t w) : cutKey r t = cutKey w h := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let y : Height := ⟨i / 7, by change i / 7 < 7; omega⟩
  let z : Height := ⟨i % 7, Nat.mod_lt _ (by decide)⟩
  have hij : 7 * y.val + z.val = i := Nat.div_add_mod i 7
  apply Bool.eq_iff_iff.mpr
  rw [← hij, cutKey_bit, cutKey_bit, hr, hr, hw, hw]
  tauto

/-- Reject when there is no transverse witness for these two cuts. -/
def rejectsDomain (s t : Cube) (mark : Height) (domain : Array Cube) : Bool :=
  domain.all fun w => !(cutKey s mark == cutKey w 0 && cutKey t mark == cutKey w 3)

/-- This conclusion is conditional on actual membership in the checked domain.
Coverage of omitted representatives or motions must be proved separately. -/
theorem rejectsDomain_sound {s t : Cube} {mark : Height} {domain : Array Cube}
    (hc : rejectsDomain s t mark domain = true) {C : Words}
    (hs : Anchor C 0 s) (ht : Anchor C 3 t) {w : Cube} (hw : w ∈ domain) :
    ¬ Transverse C mark w := by
  intro hwC
  have h := Array.all_eq_true_iff_forall_mem.mp hc w hw
  simp [crossing_eq hs hwC, crossing_eq ht hwC] at h

end SevenCycle.TypeThree

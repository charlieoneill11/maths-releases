import Init

/-! Executable matching-bit constraints for the type-two search. -/

namespace SevenCycle.TypeTwo

abbrev Mask := BitVec 33

def pop (m : Mask) : Nat := m.cpop.toNat

structure Mark where
  leftSeen : Mask
  rightSeen : Mask
  leftIn : Mask
  rightIn : Mask
  deriving Inhabited

def empty : Mark := ⟨0, 0, 0, 0⟩

def combine (a b : Mark) : Mark :=
  ⟨a.leftSeen ||| b.leftSeen, a.rightSeen ||| b.rightSeen,
    a.leftIn ||| b.leftIn, a.rightIn ||| b.rightIn⟩

def agreeOn (seen seen' val val' : Mask) : Bool :=
  ((val ^^^ val') &&& seen &&& seen') == 0

def agrees (a b : Mark) : Bool :=
  agreeOn a.leftSeen b.leftSeen a.leftIn b.leftIn &&
    agreeOn a.rightSeen b.rightSeen a.rightIn b.rightIn

def viable (a : Mark) : Bool :=
  a.leftIn &&& a.rightIn == 0 &&
    pop (a.leftSeen &&& a.rightSeen &&& ~~~(a.leftIn ||| a.rightIn)) ≤ 2 &&
    pop a.leftIn ≤ 19 && pop a.rightIn ≤ 19 &&
    14 ≤ 33 - pop (a.leftSeen &&& ~~~a.leftIn) &&
    14 ≤ 33 - pop (a.rightSeen &&& ~~~a.rightIn)

/-- Try bands in decreasing array index. An empty candidate list rejects the branch. -/
def hasPrefix (bands : Array (Array Mark)) : Nat → Mark → Bool
  | 0, _ => true
  | n+1, a => (bands[n]?.getD #[]).any fun b =>
      agrees a b && viable (combine a b) && hasPrefix bands n (combine a b)

/-- True certifies that these band restrictions have no legal common assignment. -/
def rejectsLayout (bands : Array (Array Mark)) : Bool :=
  !(hasPrefix bands bands.size empty)

end SevenCycle.TypeTwo

import SevenCycleRuntime.TypeThree

/-! Necessary planar crossings between the six marked transverse projections. -/

namespace SevenCycle.TypeTwo.Cross

abbrev Cube := Vector UInt64 7
abbrev Slot := Fin 3 × Fin 7
abbrev Marks := Vector Slot 6
abbrev Domains := Vector (Array Cube) 6

def otherAxis (a b : Fin 3) : Fin 3 := if b < a then b+1 else b

structure Row where
  pos : Fin 6
  keys : Vector UInt64 6

def row (marks : Marks) (i : Fin 6) (c : Cube) : Row :=
  ⟨i,Vector.ofFn fun j =>
    TypeThree.fastCut c (otherAxis marks[i].1 marks[j].1) marks[j].2⟩

def fits (marks : Marks) (a b : Row) : Bool :=
  marks[a.pos].1 == marks[b.pos].1 || a.keys[b.pos] == b.keys[a.pos]

def search (marks : Marks) (domains : Vector (Array Row) 6) : Nat → Array Row → Bool
  | 0, _ => true
  | n+1, prev =>
    (domains[Fin.ofNat 6 n]).any fun b =>
      prev.all (fits marks b) && search marks domains n (prev.push b)

def reject (marks : Marks) (domains : Domains) : Bool :=
  let d := Vector.ofFn fun j => domains[j].map (row marks j)
  !(search marks d 6 #[])

end SevenCycle.TypeTwo.Cross

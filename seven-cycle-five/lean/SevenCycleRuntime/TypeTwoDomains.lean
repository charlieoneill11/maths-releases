import SevenCycleRuntime.TypeTwo
import SevenCycleRuntime.TypeThree

namespace SevenCycle.TypeTwo.Packed

abbrev Cube := Vector UInt64 7
abbrev Key := UInt64 × UInt64
abbrev Domains := Std.HashMap Key (Array Cube)

def key (w : Cube) : Key := (TypeThree.fastCut w 0 0, TypeThree.fastCut w 0 2)

def extend (keys : Std.HashMap Key Unit) (m : Domains) (w : Cube) : Domains :=
  let k := key w
  if keys.contains k then m.alter k fun old => some ((old.getD #[]).push w)
  else m

/-- Build only buckets queried by this batch. At most one full orbit of
transformed cubes is allocated in addition to the retained candidates. -/
def collect (images : Cube → Array Cube) (sources : Array Cube) (keys : Std.HashMap Key Unit) : Domains :=
  sources.foldl (init := {}) fun m r => (images r).foldl (extend keys) m

def wanted (s t : Cube) (marks : Vector (Fin 3 × Fin 7) 6) : Std.HashMap Key Unit :=
  marks.toArray.foldl (init := {}) fun m (a,j) =>
    m.insert (TypeThree.fastCut s a j, TypeThree.fastCut t a j) ()

end SevenCycle.TypeTwo.Packed

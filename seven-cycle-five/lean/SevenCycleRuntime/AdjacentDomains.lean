import SevenCycleRuntime.Contacts
import SevenCycleRuntime.AdjacentBands

namespace SevenCycle.Adjacent.BandJoin

structure Prefix where
  first : UInt64
  second : UInt64
  middle : UInt64
deriving DecidableEq, Hashable, Inhabited

instance : BEq Prefix where
  beq p q := p.first == q.first && p.second == q.second && p.middle == q.middle

instance : LawfulBEq Prefix where
  rfl := by intro p; change (_ && _ && _) = true; simp
  eq_of_beq := by
    rintro ⟨a,b,c⟩ ⟨d,e,f⟩ h
    change ((a == d && b == e) && c == f) = true at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨rfl,rfl⟩,rfl⟩
    rfl

@[inline] def prefixOf (w : PackedCube) : Prefix :=
  ⟨SevenCycle.TypeThree.cutX w 0, SevenCycle.TypeThree.cutX w 1, Contacts.middle w⟩

@[inline] def request (s t u : PackedCube) (p : Port) : Prefix :=
  ⟨SevenCycle.TypeThree.fastCut s p.axis p.start, SevenCycle.TypeThree.fastCut t p.axis p.start,
    SevenCycle.TypeThree.fastCut u p.axis p.start⟩

abbrev Index := Std.HashMap Prefix (Array PackedCube)

def insertIf (needed : Prefix → Bool) (m : Index) (w : PackedCube) : Index :=
  let k := prefixOf w
  if needed k then m.alter k (fun old => some ((old.getD #[]).push w)) else m

def indexPrefixes (orbits : PackedCube → Array PackedCube) (needed : Prefix → Bool)
    (reps : Array PackedCube) : Index :=
  reps.foldl (init := {}) fun m r => (orbits r).foldl (insertIf needed) m

/-- An unindexed key is sent to the continuation, so a sparse hint controls
work only. A successful six-band join is likewise sent to the continuation. -/
def gate (needed : Prefix → Bool) (idx : Index) (s t u : PackedCube) (ports : Ports)
    (keep : Unit → Bool) : Bool :=
  let keys := ports.map (request s t u)
  if keys.toArray.all needed then
    !(canJoin ports (keys.map fun k => idx.getD k #[])) || keep ()
  else keep ()

end SevenCycle.Adjacent.BandJoin

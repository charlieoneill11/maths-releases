import Std.Data.HashMap.Basic

/-! Packed planar-support filtering for all source representatives at once. -/

namespace SevenCycle.TypeTwo.Planar

abbrev Grid := Vector (Vector UInt64 7) 3
abbrev PartnerTable := Std.HashMap UInt64 (Array UInt64)
abbrev CandidateIndex := Vector (Vector (Std.HashMap UInt64 Nat) 7) 3

def addBit (m : Std.HashMap UInt64 Nat) (i : Nat) (right : UInt64) : Std.HashMap UInt64 Nat :=
  m.alter right fun old => some ((old.getD 0) ||| (2^i))

def addPartners (m : Std.HashMap UInt64 Nat) (i : Nat) (right : Array UInt64) : Std.HashMap UInt64 Nat :=
  right.foldl (fun m k => addBit m i k) m

/-- Each bit in the result is the index of a source cube. The partner lists
need only contain every permitted second mask for their first mask. -/
def candidateIndex (partners : PartnerTable) (sources : Array Grid) : CandidateIndex :=
  Vector.ofFn fun a => Vector.ofFn fun j =>
    (Array.finRange sources.size).foldl (init := {}) fun m i =>
      addPartners m i.val (partners.getD sources[i][a][j] #[])

@[inline] def eligibleAxis (v : Vector Nat 7) : Nat :=
  let atStart (t : Fin 7) := v[t] &&& (v[t+2] ||| v[t+3])
  atStart 0 ||| atStart 1 ||| atStart 2 ||| atStart 3 |||
    atStart 4 ||| atStart 5 ||| atStart 6

/-- A bit survives if each of the three transverse axes admits two marked
contacts at separation two or three. The source axis already has separation two. -/
def eligibleSources (idx : CandidateIndex) (t : Grid) : Nat :=
  let marks (a : Fin 3) := Vector.ofFn fun j : Fin 7 => idx[a][j].getD t[a][j] 0
  eligibleAxis (marks 0) &&& eligibleAxis (marks 1) &&& eligibleAxis (marks 2)

structure Pick where
  first : Fin 7
  far : Bool
  deriving Inhabited, DecidableEq

@[inline] def Pick.last (p : Pick) : Fin 7 := p.first + (if p.far then 3 else 2)

def picks (allowed : Fin 7 → Bool) : Array Pick :=
  (Array.finRange 7).flatMap fun t => (#[false,true] : Array Bool).filterMap fun far =>
    let p := (⟨t,far⟩ : Pick)
    if allowed t && allowed p.last then some p else none

def placements (idx : CandidateIndex) (i : Nat) (t : Grid) : Array (Vector Pick 3) :=
  let localPicks (a : Fin 3) := picks (fun j => (idx[a][j].getD t[a][j] 0).testBit i)
  let a := localPicks 0
  let b := localPicks 1
  let c := localPicks 2
  a.flatMap fun i => b.flatMap fun j => c.map fun k => #v[i,j,k]

end SevenCycle.TypeTwo.Planar

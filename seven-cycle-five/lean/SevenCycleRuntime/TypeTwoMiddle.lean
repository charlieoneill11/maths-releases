import SevenCycleRuntime.TypeTwoDomains
import SevenCycleRuntime.TypeTwoGraph
import SevenCycleRuntime.TypeTwoMatching

/-! Building the two middle-level domains from the moved atlas supports. -/

namespace SevenCycle.TypeTwo.Mid

open Graph (Cube Site Sites)
open Packed (Key)

abbrev MiddlePair := UInt64 × UInt64
abbrev Index := Std.HashMap Key (Array MiddlePair)
abbrev Allowed := Std.HashMap UInt64 Unit

/-- Only first masks that occur on the source representatives can be queried. -/
def allowed (sources : Array Planar.Grid) : Allowed :=
  sources.foldl (init := {}) fun m g =>
    g.toArray.foldl (init := m) fun m row =>
      row.toArray.foldl (fun m u => m.insert u ()) m

def extend (wants : Allowed) (m : Index) (r : Cube) : Index :=
  let k := Packed.key r
  if wants.contains k.1 then
    let v := (r[1], r[2])
    m.alter k fun old =>
      let a := old.getD #[]
      some (if a.contains v then a else a.push v)
  else m

/-- Store two single planes per distinct option, with one orbit in working memory. -/
def index (images : Cube → Array Cube) (sources : Array Cube) (wants : Allowed) : Index :=
  sources.foldl (init := {}) fun m r => (images r).foldl (extend wants) m

def partners (m : Index) : Planar.PartnerTable :=
  m.keysArray.foldl (init := {}) fun m k =>
    m.alter k.1 fun a => some ((a.getD #[]).push k.2)

def sites (r : Cube) : Option Sites :=
  let xs := (Array.finRange 343).filter (Graph.present r)
  if h : xs.size = 33 then some ⟨xs,h⟩ else none

@[inline] def flatten (a : Fin 3) (x : Site) : Nat :=
  if a = 0 then x.val % 49
  else if a = 1 then (x.val / 49)*7 + x.val % 7
  else x.val / 7

def bits (p : Nat → Bool) : (n : Nat) → BitVec n
  | 0 => 0
  | n+1 => BitVec.cons (p n) (bits p n)

@[inline] def view (xs : Sites) (a : Fin 3) (t : Fin 7) : Mask :=
  bits (fun i =>
    let v := Graph.coord xs[Fin.ofNat 33 i] a
    v == t || v == t+1) 33

@[inline] def read (xs : Sites) (a : Fin 3) (v : UInt64) : Mask :=
  bits (fun i => v.toNat.testBit (flatten a xs[Fin.ofNat 33 i])) 33

def row (xs ys : Sites) (a : Fin 3) (t : Fin 7) (candidates : Array MiddlePair) : Array Mark :=
  let seenX := view xs a t
  let seenY := view ys a t
  candidates.map fun (p,q) => ⟨seenX, seenY, seenX &&& read xs a p, seenY &&& read ys a q⟩

abbrev Rows := Vector (Vector (Array Mark) 7) 3

def rows (m : Index) (left right : Planar.Grid) (xs ys : Sites) : Rows :=
  Vector.ofFn fun a => Vector.ofFn fun t =>
    row xs ys a t (m.getD (left[a][t], right[a][t]) #[])

def contacts (p : Vector Planar.Pick 3) : Vector (Fin 3 × Fin 7) 6 :=
  #v[(0,p[0].first), (0,p[0].last), (1,p[1].first), (1,p[1].last),
     (2,p[2].first), (2,p[2].last)]

def reject (r : Rows) (p : Vector Planar.Pick 3) : Bool :=
  rejectsLayout ((contacts p).toArray.map fun (a,t) => r[a][t])

end SevenCycle.TypeTwo.Mid

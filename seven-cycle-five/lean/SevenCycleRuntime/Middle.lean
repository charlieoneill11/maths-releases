import SevenCycleRuntime.Contacts
import SevenCycleRuntime.Adjacent

namespace SevenCycle.Adjacent.Middle

open Contacts (Cube Height Index)

structure Site where
  x : Height
  y : Height
  z : Height
  deriving Inhabited, DecidableEq

@[inline] def occupied (u : Cube) (v : Site) : Bool :=
  (u.get v.x).toNat.testBit (7*v.y.val+v.z.val)

def sites (s : Cube) : Array Site :=
  (Array.finRange 7).flatMap fun x => (Array.finRange 7).flatMap fun y =>
    ((Array.finRange 7).map fun z => Site.mk x y z).filter (occupied s)

@[inline] def axisValue (k : Fin 3) (v : Site) : Height :=
  match k.val with | 0 => v.x | 1 => v.y | _ => v.z

@[inline] def projectedIndex (k : Fin 3) (v : Site) : Nat :=
  match k.val with
  | 0 => 7*v.y.val+v.z.val
  | 1 => 7*v.x.val+v.z.val
  | _ => 7*v.x.val+v.y.val

@[inline] def inWindow (k : Fin 3) (j : Height) (v : Site) : Bool :=
  axisValue k v == j || axisValue k v == j+1

/-- One tag per anchor site; the middle assignments fit in 33 bits. -/
@[inline] def flags {α : Type} (rows : Array α) (p : α → Bool) : Nat :=
  rows.foldr (fun x n => 2*n+(p x).toNat) 0

structure Choices where
  scope : Nat
  picks : Array Nat

/-- A projected mask fixes both selected and absent sites within this window. -/
def choices (anchors : Array Site) (s t : Cube) (idx : Index) (a : Fin 3) (j : Height) : Choices :=
  let scope := flags anchors (inWindow a j)
  let patterns := idx.getD (Contacts.anchorKey s t a j) #[]
  ⟨scope, patterns.map fun p => flags anchors fun v =>
    inWindow a j v && p.toNat.testBit (projectedIndex a v)⟩

@[inline] def mergeable (fixed selected scope pick : Nat) : Bool :=
  (selected &&& scope) == (pick &&& fixed)

/-- Complete remaining bits. The branch with a forced absent bit is skipped. -/
def complete (next : Nat → Bool) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, acc => next acc
  | n+1, remaining, tag, acc =>
    if remaining = 0 then next acc
    else complete next n (remaining/2) (2*tag) acc &&
      (!(remaining.testBit 0) || complete next n (remaining/2) (2*tag) (acc + tag))

/-- One partial assignment must agree on both supports and all earlier rows. -/
@[inline] def checkRow (common : Nat) (row : Choices) (rest : Nat → Nat → Bool)
    (fixed selected : Nat) : Bool :=
  row.picks.all fun p =>
    (p &&& common) != p || !(mergeable fixed selected row.scope p) ||
      rest (fixed ||| row.scope) (selected ||| p)

/-- Compose the six window checks directly from their array. -/
def walkRows (common : Nat) (visit : Nat → Nat → Bool) (rows : Array Choices) : Nat → Nat → Bool :=
  rows.foldr (checkRow common) visit

def join (common n : Nat) (next : Nat → Bool) (rows : Array Choices) : Nat → Nat → Bool :=
  walkRows common (fun fixed selected =>
    complete (fun extra => next (selected ||| extra)) n (common ^^^ (common &&& fixed)) 1 0) rows

@[inline] def materialize (xs : Array Site) (bits : Nat) : Cube :=
  (xs.zipIdx).foldl (init := Vector.replicate 7 0) fun state (pt,i) =>
    if bits.testBit i then
      state.set pt.x.val ((state.get pt.x) ||| (2^(7*pt.y.val+pt.z.val) : Nat).toUInt64)
    else state

@[inline] def count (u : Cube) : Nat :=
  SevenCycleRuntime.Adjacent.maskCard (u.get 0) + SevenCycleRuntime.Adjacent.maskCard (u.get 1) +
  SevenCycleRuntime.Adjacent.maskCard (u.get 2) + SevenCycleRuntime.Adjacent.maskCard (u.get 3) +
  SevenCycleRuntime.Adjacent.maskCard (u.get 4) + SevenCycleRuntime.Adjacent.maskCard (u.get 5) +
  SevenCycleRuntime.Adjacent.maskCard (u.get 6)

/-- Inputs are the later starts in the three transverse directions. -/
def checkMiddle (s t : Cube) (idx : Index) (gaps cs : Vector Height 3) (next : Cube → Bool) : Bool :=
  let xs := sites s
  let common := flags xs (occupied t)
  let windows := (Array.finRange 3).flatMap fun a =>
    #[choices xs s t idx a (cs.get a - gaps.get a), choices xs s t idx a (cs.get a)]
  join common xs.size (fun bits =>
    let u := materialize xs bits
    let n := count u
    n < 16 || 19 < n || next u) windows 0 0

end SevenCycle.Adjacent.Middle

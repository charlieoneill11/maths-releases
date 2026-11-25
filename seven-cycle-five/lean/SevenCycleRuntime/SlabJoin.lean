import Std.Data.HashMap
import Std.Data.HashSet

namespace SevenCycle.Adjacent.SlabJoin

structure Slab where
  bits : Nat
  k0 : UInt64
  k1 : UInt64
  k2 : UInt64
  k3 : UInt64
deriving Inhabited

@[inline] def digest (bits face : Nat) : UInt64 := ((bits &&& face) % 18446744073709551557).toUInt64

@[inline] def cached (r : Vector Nat 4) (bits : Nat) : Slab :=
  ⟨bits,digest bits r[0],digest bits r[1],digest bits r[2],digest bits r[3]⟩

@[inline] def faceKey (s : Slab) (k : Fin 4) : UInt64 :=
  match k.val with
  | 0 => s.k0 | 1 => s.k1 | 2 => s.k2 | _ => s.k3

def indexBy {α β : Type} [BEq α] [Hashable α] (rows : Array β) (f : β → α) :
    Std.HashMap α (Array β) :=
  rows.foldl (fun m r => m.alter (f r) fun old => some ((old.getD #[]).push r)) {}

def checkJoin (a b c d : Array Slab) (leaf : Nat → Bool) : Bool :=
  let ib := indexBy b Slab.k0
  let ic := indexBy c fun r => (r.k0,r.k1)
  let id := indexBy d fun r => (r.k0,r.k1,r.k2)
  a.all fun s => (ib.getD s.k1 #[]).all fun t =>
    (ic.getD (s.k2,t.k2) #[]).all fun u =>
    (id.getD (s.k3,t.k3,u.k3) #[]).all fun v => leaf (s.bits ||| t.bits ||| u.bits ||| v.bits)

abbrev Domains := Vector (Array Slab) 4

def pruneStep (d : Domains) (a b : Fin 4) : Domains :=
  if a = b then d else
    let keys := d[b].foldl (init := ({} : Std.HashSet UInt64)) (fun seen r => seen.insert (faceKey r a))
    d.set a (d[a].filter fun r => keys.contains (faceKey r b))

def prunePass (d : Domains) : Domains :=
  (Array.finRange 4).foldl (fun cur a =>
    (Array.finRange 4).foldl (fun cur b => pruneStep cur a b) cur) d

def prune : Nat → Domains → Domains
  | 0, d => d
  | n+1, d => prune n (prunePass d)

def maskUpTo (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => maskUpTo p n ||| (if p n then 1 <<< n else 0)

@[inline] def coords (j : Nat) (a : Fin 4) : Nat :=
  match a.val with
  | 0 => j/343 | 1 => j/49%7 | 2 => j/7%7 | _ => j%7

@[inline] def consecutive (x y : Nat) : Bool :=
  x == y || (x+1)%7 == y || (y+1)%7 == x

@[inline] def conflictIDs (p q : Nat) : Bool :=
  p != q && consecutive (coords p 0) (coords q 0) && consecutive (coords p 1) (coords q 1) &&
  consecutive (coords p 2) (coords q 2) && consecutive (coords p 3) (coords q 3)

def neighborTable : Array Nat :=
  (Array.range 2401).map fun j => maskUpTo (conflictIDs j) 2401

def blocksFrom (neighbors : Array Nat) (bits : Nat) : Nat :=
  (Array.range 2401).foldl (init := 0) fun blocked j =>
    if bits.testBit j then blocked ||| neighbors[j]?.getD 0 else blocked

/-- Individual banned slots are computed for the surviving domains only. -/
structure Active where
  slab : Slab
  ban : Nat

def active (neighbors : Array Nat) (r : Slab) : Active := ⟨r, blocksFrom neighbors r.bits⟩

def checkActive (a b c d : Array Active) (leaf : Nat → Bool) : Bool :=
  let ib := indexBy b (fun v => v.slab.k0)
  let ic := indexBy c fun r => (r.slab.k0,r.slab.k1)
  let id := indexBy d fun r => (r.slab.k0,r.slab.k1,r.slab.k2)
  a.all fun s => (ib.getD s.slab.k1 #[]).all fun t =>
    (t.slab.bits &&& s.ban != 0) ||
    (ic.getD (s.slab.k2,t.slab.k2) #[]).all fun u =>
      (u.slab.bits &&& (s.ban ||| t.ban) != 0) ||
      (id.getD (s.slab.k3,t.slab.k3,u.slab.k3) #[]).all fun v =>
        (v.slab.bits &&& (s.ban ||| t.ban ||| u.ban) != 0) ||
        leaf (s.slab.bits ||| t.slab.bits ||| u.slab.bits ||| v.slab.bits)

def checkSlabs (d : Domains) (neighbors : Array Nat) (leaf : Nat → Bool) : Bool :=
  let x := (prune 4 d).map (·.map (active neighbors))
  checkActive x[0] x[1] x[2] x[3] leaf

end SevenCycle.Adjacent.SlabJoin

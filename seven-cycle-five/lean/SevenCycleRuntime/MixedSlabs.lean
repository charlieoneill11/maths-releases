import SevenCycleRuntime.Frames

namespace SevenCycle.Adjacent.MixedSlabs
open SlabJoin

abbrev Profile := Vector (Fin 7) 4

@[inline] def sameProfile (p : Profile) (o : AxisOrder) : Bool :=
  (Array.finRange 4).all fun k => p.get k == p.get o[k]

def transforms (p : Profile) (k : Fin 4) : Array (AxisOrder × Nat) :=
  if k = 0 then #[(identityOrder,0)] else
    (orders.filter fun o => o[k] == 0 && sameProfile p o).flatMap fun o =>
      (Array.range 16).map fun s => (o,s)

@[inline] def imageSite (p : Profile) (o : AxisOrder) (s j : Nat) : Nat :=
  let d := fun k : Fin 4 =>
    let x := coords j o[k]
    if s.testBit k.val then (15 - (p.get k).val - x) % 7 else x
  343*d 0 + 49*d 1 + 7*d 2 + d 3

def addressMap (p : Profile) (o : AxisOrder) (s : Nat) : Array Nat :=
  (Array.range 2401).map fun j => 1 <<< imageSite p o s j

def domain (rows : Array (Array Nat)) (p : Profile) (k : Fin 4) : Array Slab :=
  let entries := (transforms p k).flatMap fun (o,s) =>
    let map := addressMap p o s
    rows.map fun r => FrameMask.mk (movedMask map r)
  (Std.HashSet.ofArray entries).toArray.map fun r => cached regionMasks r.bits

@[inline] def fits (a b : Active) (i j : Fin 4) : Bool :=
  faceKey a.slab j == faceKey b.slab i && (a.slab.bits &&& b.ban) == 0

/-- Join the two or three marked slabs. The remaining-band check depends only
on their physical union. -/
def check (p : Profile) (table : Array String) (leaf : Nat → Bool) : Bool :=
  let rows := table.map readSlab
  let a := (domain rows p 0).map (active neighborTable)
  let b := (domain rows p 1).map (active neighborTable)
  let c := if p.get 2 == 1 then (domain rows p 2).map (active neighborTable) else #[]
  a.all fun x => b.all fun y =>
    !(fits x y 0 1) || if p.get 2 == 1 then c.all fun z =>
        !(fits x z 0 2 && fits y z 1 2) || leaf (x.slab.bits ||| y.slab.bits ||| z.slab.bits)
      else leaf (x.slab.bits ||| y.slab.bits)

end SevenCycle.Adjacent.MixedSlabs

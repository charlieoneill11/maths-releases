import SevenCycleRuntime.TypeThree

/-! # Adaptive selection of the first two crossings

For each source choose any two slots. Sources choosing the same pair share an
opposite-anchor index. At most one such index is live in addition to the domain
index. The cost estimate affects only the order in which candidates are tested. -/

namespace SevenCycle.TypeThree

abbrev SlotPair := Fin 6 × Fin 6
abbrev SlotCosts := Std.HashMap UInt64 Nat

/-- Number of opposite anchors expected to pass a slot, using the multiplicity
of each possible partner mask at the first anchor slot. -/
def estimateSlots (d : Index) (all : Array CutRow) : SlotCosts :=
  let freq : SlotCosts := all.foldl (fun m r =>
    m.alter r.a0 fun n => some (n.getD 0 + 1)) {}
  d.fold (fun acc x partners =>
    let count := partners.fold (fun n y _ => n + freq.getD y 0) 0
    acc.insert x count) {}

def leastSlots (cost : SlotCosts) (s : CutRow) : SlotPair := Id.run do
  let score := fun i => cost.getD (slot s i) 0
  let mut p : SlotPair := if score 0 ≤ score 1 then (0, 1) else (1, 0)
  for i in (#[(2 : Fin 6), 3, 4, 5]) do
    if score i < score p.1 then
      p := (i, p.1)
    else if score i < score p.2 then
      p := (p.1, i)
  return if p.1 < p.2 then p else p.swap

def selected (tagged : Array (SlotPair × CutRow)) (ij : SlotPair) : Array CutRow :=
  tagged.filterMap fun entry => if entry.1 = ij then some entry.2 else none

/-- The pair (0,1) uses the domain index itself. Other query indices are
constructed on demand, only for nonempty groups. -/
def queryIndex (rows : Array CutRow) (domains : Index) (ij : SlotPair) : Index :=
  if ij = (0,1) then domains else makeIndex (slot · ij.1) (slot · ij.2) rows

def evaluateGroups (allow : SlotPair → Bool) (rows : Array CutRow) (domains : Index)
    (tagged : Array (SlotPair × CutRow)) : Bool :=
  (Array.finRange 6).all fun i => (Array.finRange 6).all fun j =>
    !allow (i,j) ||
      let group := selected tagged (i,j)
      if group.isEmpty then true else
        let query := queryIndex rows domains (i,j)
        group.all (rejectsSource domains query i j)

def adaptiveSources (choose : Index → Array CutRow → CutRow → SlotPair)
    (sources rows : Array CutRow) : Bool :=
  let domains := makeIndex CutRow.a0 CutRow.a3 rows
  let tagged := sources.map fun s => (choose domains rows s, s)
  evaluateGroups (fun _ => true) rows domains tagged

/-- Accept the computed table as a value. Passing a curried scoring function
here would let partial application defer its construction to each source. -/
@[noinline] def tagByCost (cost : SlotCosts) (sources : Array CutRow) : Array (SlotPair × CutRow) :=
  sources.map fun s => (leastSlots cost s, s)

def checkGroups (allow : SlotPair → Bool) (sources rows : Array CutRow) : Bool :=
  let domains := makeIndex CutRow.a0 CutRow.a3 rows
  let cost := estimateSlots domains rows
  evaluateGroups allow rows domains (tagByCost cost sources)

/-- The fifteen strictly increasing slot pairs, in lexicographic order,
are assigned three per part. The formula also assigns all other pairs. -/
def slotPart (ij : SlotPair) : Fin 5 :=
  let i := min ij.1.val ij.2.val
  let j := max ij.1.val ij.2.val
  Fin.ofNat 5 ((i * (11 - i) / 2 + (j - (i + 1))) / 3)

def checkAdaptive (sources rows : Array CutRow) : Bool :=
  checkGroups (fun _ => true) sources rows

def checkPart (part : Fin 5) (sources rows : Array CutRow) : Bool :=
  checkGroups (fun ij => slotPart ij == part) sources rows

end SevenCycle.TypeThree

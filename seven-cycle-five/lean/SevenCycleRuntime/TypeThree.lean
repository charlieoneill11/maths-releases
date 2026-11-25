import Std.Data.HashMap

/-! Executable type-three masks, support indices and joins. The correctness
proofs against the geometric definitions are in `SevenCycle.TypeThree`. -/

namespace SevenCycle.TypeThree

/-- Two cuts for each of the three ordered axes of a support. -/
structure CutRow where
  a0 : UInt64
  a3 : UInt64
  b0 : UInt64
  b3 : UInt64
  c0 : UInt64
  c3 : UInt64
  deriving Inhabited, BEq, DecidableEq, Hashable

def mid (r : CutRow) (far : Bool) : UInt64 := if far then r.b3 else r.b0
def last (r : CutRow) (far : Bool) : UInt64 := if far then r.c3 else r.c0

@[inline] def fitsB (a a' b : CutRow) (far : Bool) : Bool :=
  mid a far == b.b0 && mid a' far == b.b3

@[inline] def fitsC (a a' b b' c : CutRow) (far : Bool) : Bool :=
  last a far == c.b0 && last a' far == c.b3 &&
  last b far == c.c0 && last b' far == c.c3

def rejectJoin (a0 a3 b0 b3 c0 c3 : Array CutRow) : Bool :=
  !(a0.any fun a => a3.any fun a' =>
    b0.any fun b => fitsB a a' b false &&
    b3.any fun b' => fitsB a a' b' true &&
    (c0.any fun c => fitsC a a' b b' c false) &&
    (c3.any fun c' => fitsC a a' b b' c' true))

abbrev Buckets := Std.HashMap UInt64 (Array CutRow)
abbrev Index := Std.HashMap UInt64 Buckets

@[inline] def bucket (m : Index) (x y : UInt64) : Array CutRow := (m.getD x {}).getD y #[]

@[inline] def addRow (m : Index) (x y : UInt64) (r : CutRow) : Index :=
  m.alter x fun v => some ((v.getD {}).alter y fun a => some ((a.getD #[]).push r))

def makeIndex (f g : CutRow → UInt64) (rows : Array CutRow) : Index :=
  rows.foldl (fun m r => addRow m (f r) (g r) r) {}

@[inline] def slot (r : CutRow) (k : Fin 6) : UInt64 :=
  match k.val with
  | 0 => r.a0 | 1 => r.a3 | 2 => r.b0 | 3 => r.b3 | 4 => r.c0 | _ => r.c3

/-- The six left keys are fixed for every test with one source. Fetch their
partner maps once before iterating the possible opposite supports. -/
structure SourceDomains where
  a0 : Buckets
  a3 : Buckets
  b0 : Buckets
  b3 : Buckets
  c0 : Buckets
  c3 : Buckets

def sourceDomains (d : Index) (s : CutRow) : SourceDomains :=
  ⟨d.getD s.a0 {}, d.getD s.a3 {}, d.getD s.b0 {}, d.getD s.b3 {},
   d.getD s.c0 {}, d.getD s.c3 {}⟩

/-- Test the remaining transverse keys before materializing the six domains.
The first two keys are also checked by the exact join. -/
def rejectsPair (g : SourceDomains) (t : CutRow) : Bool :=
  !g.b0.contains t.b0 || !g.b3.contains t.b3 || !g.c0.contains t.c0 ||
    !g.c3.contains t.c3 ||
    rejectJoin (g.a0.getD t.a0 #[]) (g.a3.getD t.a3 #[])
      (g.b0.getD t.b0 #[]) (g.b3.getD t.b3 #[])
      (g.c0.getD t.c0 #[]) (g.c3.getD t.c3 #[])

/-- Intersect the allowed partners with the keys of one query bucket. Iterate
whichever key set is smaller and run the test on all rows of each hit. -/
def checkBuckets (allowed groups : Buckets) (ok : CutRow → Bool) : Bool :=
  if allowed.size ≤ groups.size then
    allowed.all fun y _ => (groups.getD y #[]).all ok
  else
    groups.all fun y rows => !allowed.contains y || rows.all ok

/-- Enumerate only opposite anchors in buckets allowed by two crossings. The
choice of slots affects running time and makes no assumption about a code. -/
def rejectsSource (d q : Index) (i j : Fin 6) (s : CutRow) : Bool :=
  let allowed := d.getD (slot s j) {}
  let domains := sourceDomains d s
  (d.getD (slot s i) {}).all fun x _ => checkBuckets allowed (q.getD x {}) (rejectsPair domains)

def checkSources (sources all : Array CutRow) (i j : Fin 6) : Bool :=
  let d := makeIndex CutRow.a0 CutRow.a3 all
  let q := makeIndex (slot · i) (slot · j) all
  sources.all (rejectsSource d q i j)

@[inline] def sendLine (v : UInt64) (i : Fin 7) : UInt64 :=
  (v &&& 127) <<< (7*i.val).toUInt64

@[inline] def joinLines (f : Fin 7 → UInt64) : UInt64 :=
  ((f 0 &&& (127 : UInt64)) <<< (0 : UInt64)) ||| ((f 1 &&& (127 : UInt64)) <<< (7 : UInt64)) ||| ((f 2 &&& (127 : UInt64)) <<< (14 : UInt64)) |||
    ((f 3 &&& (127 : UInt64)) <<< (21 : UInt64)) ||| ((f 4 &&& (127 : UInt64)) <<< (28 : UInt64)) ||| ((f 5 &&& (127 : UInt64)) <<< (35 : UInt64)) |||
    ((f 6 &&& (127 : UInt64)) <<< (42 : UInt64))

@[inline] def gatherBit (p : UInt64) (j : Fin 7) : UInt64 :=
  (p >>> (6*j.val).toUInt64) &&& UInt64.ofNat (2^j.val)

@[inline] def gatherColumn (p : UInt64) : UInt64 :=
  ((p >>> (0 : UInt64)) &&& (1 : UInt64)) ||| ((p >>> (6 : UInt64)) &&& (2 : UInt64)) ||| ((p >>> (12 : UInt64)) &&& (4 : UInt64)) ||| ((p >>> (18 : UInt64)) &&& (8 : UInt64)) |||
    ((p >>> (24 : UInt64)) &&& (16 : UInt64)) ||| ((p >>> (30 : UInt64)) &&& (32 : UInt64)) ||| ((p >>> (36 : UInt64)) &&& (64 : UInt64))

@[inline] def lineY (p : UInt64) (s : Fin 7) := p >>> (7*s.val).toUInt64
@[inline] def lineZ (p : UInt64) (s : Fin 7) := gatherColumn (p >>> s.val.toUInt64)

@[inline] def cutX (c : Vector UInt64 7) (s : Fin 7) : UInt64 := (c.get s ||| c.get (s+1 : Fin 7)) &&& 0x1ffffffffffff
@[inline] def cutY (c : Vector UInt64 7) (s : Fin 7) : UInt64 :=
  (joinLines fun i => lineY (c.get i) s ||| lineY (c.get i) (s+1)) &&& 0x1ffffffffffff
@[inline] def cutZ (c : Vector UInt64 7) (s : Fin 7) : UInt64 :=
  (joinLines fun i => lineZ (c.get i) s ||| lineZ (c.get i) (s+1)) &&& 0x1ffffffffffff

@[inline] def fastCut (c : Vector UInt64 7) (k : Fin 3) (s : Fin 7) : UInt64 :=
  match k.val with
  | 0 => cutX c s
  | 1 => cutY c s
  | _ => cutZ c s

def fastCutsOf (c : Vector UInt64 7) : CutRow :=
  ⟨cutX c 0, cutX c 3, cutY c 0, cutY c 3, cutZ c 0, cutZ c 3⟩

/-- Expand each supplied support and compute its cut rows within the precompiled loop. -/
def packRows (representatives : Array (Vector UInt64 7))
    (images : Vector UInt64 7 → Array (Vector UInt64 7)) : Array CutRow :=
  representatives.flatMap fun r => (images r).map fastCutsOf

end SevenCycle.TypeThree

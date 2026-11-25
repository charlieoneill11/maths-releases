import SevenCycleRuntime.AdjacentDomains
import SevenCycleRuntime.BandCounts
import SevenCycleRuntime.AdjacentScan

namespace SevenCycle.Adjacent.BandStage
open BandJoin (PackedCube Prefix Index Ports)

/-- The three centre-plane populations are determined by the two anchor
supports and the visible part of their common middle. -/
def counts (s t u : PackedCube) (cs : Scan.Marks) : Vector Nat 3 :=
  Vector.ofFn fun a => BandCounts.known s t u a (cs.get a)

def ports (s t u : PackedCube) (gaps cs : Scan.Marks) : Ports :=
  BandJoin.portsFor (Vector.ofFn fun a : Fin 3 => cs.get a - gaps.get a)
    (gaps.map Fin.val) (counts s t u cs)

/-- Send unknown prefix keys to the next stage. When the hint covers every
query, require an actual six-band join among the indexed complete bands. -/
def survives (needed : Prefix → Bool) (idx : Index) (s t : PackedCube)
    (gaps cs : Scan.Marks) (visible : PackedCube) : Bool :=
  let ps := ports s t visible gaps cs
  let keys := ps.map (BandJoin.request s t visible)
  !keys.toArray.all needed || BandJoin.canJoin ps (keys.map fun k => idx.getD k #[])

end SevenCycle.Adjacent.BandStage

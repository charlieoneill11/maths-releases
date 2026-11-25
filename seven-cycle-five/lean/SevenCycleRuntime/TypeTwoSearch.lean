import SevenCycleRuntime.TypeTwoMiddle

namespace SevenCycle.TypeTwo.Search

open Graph (Cube)
open Planar (Grid Pick)
open Mid (Index)

abbrev Placement := Vector Pick 3

def grid (r : Cube) : Grid := Vector.ofFn fun a => Vector.ofFn fun j => TypeThree.fastCut r a j

structure Layout where
  left : Cube
  right : Cube
  marks : Placement
  deriving Inhabited

/-- Iterate the occupied source indices by removing their highest bit. -/
def active (n : Nat) : Array Nat :=
  if h : n = 0 then #[]
  else (active (n % 2^n.log2)).push n.log2
termination_by n
decreasing_by exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.log2_self_le h)

def filterMiddle (m : Index) (s t : Cube) (left right : Grid) (ps : Array Placement) :
    Array Placement := Id.run do
  let some xs := Mid.sites s | return ps
  let some ys := Mid.sites t | return ps
  let some (ls,rs) := Graph.propose xs ys | return ps
  if Graph.valid s t ls rs then
    let rows := Mid.rows m left right ls rs
    return ps.filter fun p => !(Mid.reject rows p)
  return ps

def forTarget (m : Index) (ss : Array Cube) (idx : Planar.CandidateIndex) (t : Cube) : Array Layout :=
  let g := grid t
  (active (Planar.eligibleSources idx g)).flatMap fun i =>
    if let some s := ss[i]? then
      (filterMiddle m s t (grid s) g (Planar.placements idx i g)).map (fun p => ⟨s,t,p⟩)
    else #[]

/-- All source representatives share one catalog and planar index. The array
of target classes can be partitioned at any boundaries. -/
def scan (images : Cube → Array Cube) (catalogSources sources targets : Array Cube) : Array Layout :=
  let gs := sources.map grid
  let m := Mid.index images catalogSources (Mid.allowed gs)
  let idx := Planar.candidateIndex (Mid.partners m) gs
  targets.flatMap fun r => (images r).flatMap (forTarget m sources idx)

end SevenCycle.TypeTwo.Search

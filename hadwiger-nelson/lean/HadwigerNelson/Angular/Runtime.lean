import HadwigerNelson.Arithmetic.Basic
import HadwigerNelson.Data.CompleteWave

namespace HadwigerNelson.Angular
open Arithmetic

/-- A segment of the right boundary in scaled integer coordinates. -/
structure Segment where
  start : Int
  stop : Int
  left : Int
  right : Int
  deriving Inhabited

/-- Integer enclosure of twice the area above a horizontal cut after a height.
The start of a partially retained segment is interpolated upwards. -/
def Segment.area (s : Segment) (d lo : Int) : Int :=
  if s.stop ≤ lo ∨ max s.left s.right ≤ d then 0
  else if lo ≤ s.start then
    positiveArea2Up (s.left-d) (s.right-d) (s.stop-s.start)
  else
    positiveArea2Up (interpUp s.start s.left s.stop s.right lo-d) (s.right-d) (s.stop-lo)

/-- Stored extremes and the integral of twice the uncut affine profile. -/
structure Totals where
  start : Int
  stop : Int
  low : Int
  high : Int
  width : Int
  mass : Int
  deriving Inhabited

def Segment.stats (s : Segment) : Totals :=
  ⟨s.start, s.stop, min s.left s.right, max s.left s.right, s.stop-s.start,
   (s.left+s.right)*(s.stop-s.start)⟩

def Totals.join (a b : Totals) : Totals :=
  ⟨min a.start b.start, max a.stop b.stop, min a.low b.low, max a.high b.high,
   a.width+b.width, a.mass+b.mass⟩

/-- A tree is built once and shared by all angular bins. -/
inductive Segments where
  | single (segment : Segment)
  | branch (stats : Totals) (left right : Segments)
  deriving Inhabited

def Segments.stats : Segments → Totals
  | .single s => s.stats
  | .branch t _ _ => t

def Segments.join (a b : Segments) : Segments := .branch (a.stats.join b.stats) a b

def Segments.Valid : Segments → Prop
  | .single s => s.start < s.stop
  | .branch t a b => t = a.stats.join b.stats ∧ a.Valid ∧ b.Valid

/-- The plain sum used in the mathematical specification. -/
def Segments.area : Segments → Int → Int → Int
  | .single s, d, lo => s.area d lo
  | .branch _ a b, d, lo => a.area d lo + b.area d lo

/-- Whole subtrees entirely above/below the cut are evaluated in constant time. -/
def Segments.fastArea : Segments → Int → Int → Int
  | .single s, d, lo => s.area d lo
  | .branch t a b, d, lo =>
    if t.stop ≤ lo ∨ t.high ≤ d then 0
    else if lo ≤ t.start ∧ d ≤ t.low then t.mass-2*d*t.width
    else a.fastArea d lo + b.fastArea d lo

/-- A balanced interval containing 2^depth uniform profile segments. -/
def tabulate (widths : Array Nat) (step : Nat) : Nat → Nat → Segments
  | 0, i => .single ⟨i*step,(i+1)*step,widths[i]?.getD 0,widths[i+1]?.getD 0⟩
  | depth+1, i =>
    (tabulate widths step depth i).join (tabulate widths step depth (i+2^depth))

/-- The outward cosine and sine bounds, in units of 10⁻¹², on [i/N,j/N]. -/
structure Box where
  xlo : Int
  xhi : Int
  ylo : Int
  yhi : Int

def halfAngleBox (n i j : Nat) : Box :=
  let nn : Int := n
  let a : Int := i
  let b : Int := j
  let n2 := nn*nn
  let a2 := a*a
  let b2 := b*b
  let S : Int := CompleteWave.scale
  ⟨(n2-b2)*S/(n2+b2), ceilDiv ((n2-a2)*S) (n2+a2),
    2*nn*a*S/(n2+a2), ceilDiv (2*nn*b*S) (n2+b2)⟩

/-- Lower enclosure for |3/4 - sin θ| over the box. -/
def Box.shiftY (b : Box) : Int :=
  let y : Int := 750000000000
  max 0 (max (y-b.yhi) (b.ylo-y))

def Box.shiftX (b : Box) : Int := 2*(CompleteWave.xInt : Int)-b.xhi

def boxArea (tree : Segments) (b : Box) : Int :=
  tree.fastArea b.xlo b.ylo + tree.fastArea b.shiftX b.shiftY

/-- A coarse block can be discarded when each of its profile segments has
ended before the lower height or lies entirely below the horizontal cut. -/
def Segments.misses : Segments → Int → Int → Bool
  | .single s, d, lo => decide (s.stop ≤ lo ∨ max s.left s.right ≤ d)
  | .branch t a b, d, lo =>
    decide (t.stop ≤ lo ∨ t.high ≤ d) || (a.misses d lo && b.misses d lo)

def skipped (tree : Segments) (b : Box) : Bool :=
  tree.misses b.xlo b.ylo && tree.misses b.shiftX b.shiftY

def weightedBin (tree : Segments) (n j : Nat) : Nat :=
  let area := boxArea tree (halfAngleBox n j (j+1))
  (ceilDiv (area*n) ((n:Int)*n+(j:Int)*j)).toNat

/-- Tail-recursive evaluation permits a fixed-size shard to use constant stack. -/
def rangeSum (f : Nat → Nat) (i count : Nat) : Nat :=
  go i count 0
where
  go (j : Nat) : Nat → Nat → Nat
    | 0, acc => acc
    | k+1, acc => go (j+1) k (acc+f j)

/-- Evaluate one group of fine bins; the coarse branch certifies both overlaps vanish. -/
def blockSum (tree : Segments) (n blockSize k : Nat) : Nat :=
  let first := k*blockSize
  if skipped tree (halfAngleBox n first (first+blockSize)) then 0
  else rangeSum (weightedBin tree n) first blockSize

def angularSum (profile : Array Nat) (n : Nat) : Nat :=
  let tree := tabulate profile CompleteWave.step 11 0
  let stride := n/4096
  rangeSum (blockSum tree n stride) 0 4096


end HadwigerNelson.Angular

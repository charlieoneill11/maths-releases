import HadwigerNelson.Angular.Runtime
import HadwigerNelson.Data.PartialWave

namespace HadwigerNelson.Angular.Partial
open Arithmetic

abbrev rightStep : Nat := 976562500
abbrev leftStep : Nat := 540000000
abbrev height : Nat := 500000000000
abbrev cutoff : Nat := 17*leftStep
abbrev bins : Nat := 2^26
abbrev groupSize : Nat := 2^21
abbrev blockSize : Nat := 2^14

def rightValues : Array Nat := PartialWave.rightKnots.map Prod.snd
def leftValues : Array Nat := PartialWave.leftKnots.map Prod.snd

structure Walls where
  left : Array Nat
  right : Array Nat
  tree : Segments

def walls : Walls := ⟨leftValues, rightValues, tabulate rightValues rightStep 9 0⟩

def foldedSegment (w : Walls) (lo : Nat) (i : Nat) : Segment :=
  ⟨lo+i*leftStep,lo+(i+1)*leftStep,w.left[i]?.getD 0,w.left[i+1]?.getD 0⟩

def rightSegment (w : Walls) (q : Nat) : Segment :=
  ⟨q*rightStep,(q+1)*rightStep,w.right[q]?.getD 0,w.right[q+1]?.getD 0⟩

def gapUpper (r l : Segment) (d : Int) (z : Nat) : Int :=
  interpUp r.start r.left r.stop r.right z - interpDown l.start l.left l.stop l.right z - d

def jointArea (r l : Segment) (d : Int) (a b : Nat) : Nat :=
  if a < b then (positiveArea2Up (gapUpper r l d a) (gapUpper r l d b) ((b:Int)-a)).toNat else 0

/-- A lower-wall cell meets at most two right-wall cells because its width
is 540000000 ticks and each right-wall cell has width 976562500. -/
def rowArea (w : Walls) (d : Int) (lo i : Nat) : Nat :=
  let a := min height (lo+i*leftStep)
  let b := min height (lo+(i+1)*leftStep)
  if a < b then
    let q := a / rightStep
    let m := min b ((q+1)*rightStep)
    let l := foldedSegment w lo i
    jointArea (rightSegment w q) l d a m + jointArea (rightSegment w (q+1)) l d m b
  else 0

/-- Omit the nonnegative reflected upper-half left wall, integrate its first
17 translated segments, and bound the remaining integral by the right wall. -/
def slice (w : Walls) (d lo : Int) : Nat :=
  if w.tree.misses d lo || decide (height ≤ lo.toNat) then 0 else
    let near := rangeSum (rowArea w d lo.toNat) 0 17
    near + (w.tree.fastArea d (lo.toNat+cutoff : Nat)).toNat

def shiftX (b : Box) : Int := 2*(PartialWave.xInt:Int)-b.xhi

def area (w : Walls) (b : Box) : Nat :=
  slice w b.xlo b.ylo + slice w (shiftX b) b.shiftY

def weighted (w : Walls) (n j : Nat) : Nat :=
  (ceilDiv ((area w (halfAngleBox n j (j+1)):Int)*n) ((n:Int)*n+(j:Int)*j)).toNat

/-- An angular block with a zero geometric area upper bound is empty in
every direction of the block. Other blocks use all 16,384 individual bins. -/
def block (w : Walls) (k : Nat) : Nat :=
  let j := k*blockSize
  if area w (halfAngleBox bins j (j+blockSize)) = 0 then 0 else
    rangeSum (weighted w bins) j blockSize

def groupSum (k : Nat) : Nat :=
  let w := walls
  rangeSum (block w) (k*128) 128

def checkGroup (k v : Nat) : Bool := decide (groupSum k ≤ v)

end HadwigerNelson.Angular.Partial

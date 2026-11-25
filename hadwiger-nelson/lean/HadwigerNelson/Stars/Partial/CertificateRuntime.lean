import HadwigerNelson.Stars.Partial.Moments
import HadwigerNelson.Stars.Partial.Data

/-! Four independent checks cover the signed source rows. The last also checks
the native-only rows. Degree witnesses reference a shared set of 3,171 queries. -/

namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (quant)

/-- Resetting the power cache within a shard limits peak memory. -/
def rangeState (arcs : Array BoxCheck.Arc) (start count : Nat) : Cache × Array Row :=
  count.fold (fun i _ state =>
    let (cache,r) := row arcs (source (start+i)) state.1
    (if (i+1)%2000==0 then {} else cache,state.2.push r)) ({},#[])

def rangeRows (start count : Nat) : Array Row := (rangeState arcTable start count).2

def start (part : Nat) : Nat := 35000*part
def length (part : Nat) : Nat := if part<3 then 35000 else 27621

def rowLine (r : Row) (q : Data.Query) : Int :=
  r.area*max 0 (r.mean*10000+(r.spectrum[q.harmonic]?.getD 0)*(q.threshold:Int))

def directScore (rows : Array Row) (q : Data.Query) : Int :=
  rows.foldl (fun sum r => sum+rowLine r q) 0

def rowNative (r : Row) (d : Nat) : Int := r.area*max 0 (r.mean*(d:Int)-quant)

def directNative (rows : Array Row) (d : Nat) : Int :=
  rows.foldl (fun sum r => sum+rowNative r d) 0

def checkSigned (part : Nat) (rows : Array Row) : Bool :=
  (Array.ofFn fun i : Fin Data.count =>
    let q := Data.query i.val
    decide (q.lower part ≤ directScore rows q)).all id

def checkNative (rows : Array Row) : Bool :=
  (Array.ofFn fun i : Fin 89 => decide (Data.native (i.val+1) ≤ directNative rows (i.val+1))).all id

def checkShard (part : Nat) : Bool :=
  checkSigned part (rangeRows (start part) (length part)) &&
    (part != 3 || checkNative (rangeRows 132621 4122))

def total (q : Data.Query) : Int := q.first+q.second+q.third+q.fourth

def thresholdTarget (d : Nat) (high value : Int) : Bool :=
  901*PartialWave.xInt*quant*10000*(d:Int) ≤
    (4*high*10000+2*value*(d:Int))*scale

def queryAt (ids : Array Nat) (i : Nat) : Data.Query := Data.query (ids[i]?.getD 0)

def degreePass (d : Nat) : Bool :=
  let ids := Data.degree d
  let K : Int := ids.size
  let tests := (Array.ofFn fun i : Fin ids.size =>
    let idx := ids[i.val]
    let q := Data.query idx
    idx<Data.count && q.harmonic==i.val && q.threshold≤10000 &&
      thresholdTarget d (Data.native d) (total q)).all id
  let sum := (Array.ofFn fun i : Fin ids.size =>
    let t : Int := (queryAt ids i.val).threshold
    2*(K-i.val)*t*t).sum
  0<ids.size && ids.size≤frequencyCount && tests &&
    (d:Int)*sum < (K+1-d)*(K+1)*10000^2

def dataPass : Bool :=
  (Array.ofFn fun i : Fin 88 => degreePass (i.val+1)).all id &&
    thresholdTarget 89 (Data.native 89) 0

end HadwigerNelson.Stars.PartialCheck

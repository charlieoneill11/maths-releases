import HadwigerNelson.Certificate.Hole.Tables
import HadwigerNelson.Packing.CapRuntime

namespace HadwigerNelson.Certificate.Hole

inductive Band | all | above | below

def Band.used (b : Band) (t : ℚ) : Bool :=
  match b with
  | .all => true
  | .above => decide (radiusD < t)
  | .below => decide (t ≤ radiusD)

def weightedRow (rows : Array ℤ) (b : Band) (i : Fin 16384) : ℤ :=
  let t := unitT (i.val+1)
  if b.used t then (Packing.capUpper radiusR t : ℤ)*rows[i.val+1]?.getD 0 else 0

def packingUpper (rows : Array ℤ) (b : Band) : ℚ :=
  unitWidth/(333/106)*((Array.ofFn (weightedRow rows b)).sum : ℚ)/denom

/-- Pointwise local packing is used for both total and restricted neighbour counts. -/
def checkPacking : Bool :=
  let rows := unitRows 16384
  let total := packingUpper rows .all
  decide (total ≤ 150296106235/10^18 ∧
    packingUpper rows .above ≤ 97911102803/10^18 ∧
    2*packingUpper rows .below ≤ 104770006866/10^18 ∧
    2*total ≤ 300592212470/10^18)

end HadwigerNelson.Certificate.Hole

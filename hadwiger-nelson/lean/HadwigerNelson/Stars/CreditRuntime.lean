import HadwigerNelson.Stars.MomentsRuntime

/-! The five complete-wave Fourier threshold vectors and their exact
arithmetic tests. These are candidate witnesses, checked against the
recomputed angular enclosures by the predicates below. -/

namespace HadwigerNelson.Stars.BoxCheck

def thresholds23 : Array Int := #[
  11066, 15581, 11871, 10784, 12766, 13173, 12659, 22863, 13338, 12967, 16300, 10959,
  17186, 13023, 13268, 17093, 11936, 16628, 12564, 17371, 12440, 20560, 10013, 25061,
  9415, 25547, 10538, 21653, 12838, 19249, 11721, 18422, 12274, 16346, 15586, 14407,
  20949, 13877, 20118, 14374, 20284, 15041, 20445, 14461, 19267, 14807, 16527, 18233,
  13932, 20158, 13552, 16407, 15008, 15946, 14524, 18150]

def thresholds24 : Array Int := #[
  10808, 18048, 11553, 12339, 12452, 14537, 12539, 22260, 13335, 13569, 16338, 11581,
  17319, 13355, 13637, 16624, 12300, 16446, 12817, 17144, 12552, 20003, 10267, 24368,
  9666, 24944, 10719, 21639, 12845, 19186, 11982, 17927, 12540, 15943, 15725, 14184,
  20757, 13567, 19908, 13960, 19810, 14617, 19858, 14071, 18737, 14431, 16322, 17740,
  13955, 19608, 13534, 16150, 14797, 15730, 14673, 17704]

def thresholds25 : Array Int := #[
  9532, 15598, 10181, 10695, 10987, 12660, 11110, 19425, 11815, 11912, 14508, 10161,
  15222, 11785, 11977, 14600, 10785, 14579, 11351, 15200, 11121, 17659, 9032, 21451,
  8476, 21968, 9490, 18985, 11333, 16801, 10564, 15685, 11011, 13959, 13944, 12423,
  18300, 11885, 17596, 12223, 17481, 12833, 17384, 12438, 16372, 12791, 14285, 15629,
  12241, 17228, 11910, 14333, 12999, 13919, 12952, 15573]

def thresholds26 : Array Int := #[
  7058, 10779, 7525, 7497, 8147, 9000, 8337, 13607, 8857, 8599, 10764, 7324,
  11085, 8572, 8702, 10627, 7852, 10898, 8501, 11402, 8293, 13123, 6621, 15791,
  6172, 16124, 7102, 13759, 8388, 12171, 7791, 11347, 8064, 10107, 10433, 9003,
  13429, 8611, 13004, 8868, 12758, 9380, 12454, 9250, 11729, 9563, 10276, 11425,
  8865, 12517, 8701, 10731, 9475, 10311, 9554, 11335]

def thresholds27 : Array Int := #[
  2959, 2988, 3219, 2155, 3487, 2970, 3612, 4352, 3739, 3105, 4174, 2632,
  4212, 3097, 3360, 3802, 3006, 4235, 3585, 4740, 3518, 5726, 2597, 6592,
  2360, 6414, 2956, 5345, 3470, 4813, 3148, 4495, 3195, 3901, 4271, 3400,
  4955, 3266, 4781, 3469, 4530, 3742, 4419, 3865, 4218, 4093, 3709, 4681,
  3265, 4982, 3259, 4392, 3590, 4100, 3731, 4343]

def thresholds (d : Nat) : Array Int :=
  match d with
  | 23 => thresholds23 | 24 => thresholds24 | 25 => thresholds25
  | 26 => thresholds26 | _ => thresholds27

/-- d·Q times the area-weighted positive part of f−1/d (including reflection). -/
def nativeNumerator (sat : Array (Int × Int)) (d : Int) : Int :=
  sat.foldl (fun n (a,f) => n+4*a*max 0 (f*d-quant)) 0

/-- The native contribution uses denominator x·Q·d; each signed harmonic
uses denominator x·Q·T and a factor of two for the reflected sources. -/
def targetPass (d : Int) (native weighted : Int) : Bool :=
  let x : Int := CompleteWave.xInt
  (native*thresholdScale+2*weighted*d)*10^9 ≥ 8*x*quant*thresholdScale*d

def fejerSum (ts : Array Int) : Int :=
  (Array.ofFn fun i : Fin harmonics =>
    let t := ts[i.val]?.getD 0
    2*((harmonics : Int)-i.val)*t*t).sum

def fejerPass (d : Nat) (ts : Array Int) : Bool :=
  let k : Int := harmonics
  d*fejerSum ts < (k+1-d)*(k+1)*thresholdScale*thresholdScale

def rowCredit (r : Row) (k : Nat) (t : Int) : Int :=
  r.area * max 0 (r.mean*thresholdScale+t*(r.magnitude[k]?.getD 0))

def harmonicScore (rows : Array Row) (d k : Nat) (t : Int) : Int :=
  rows.foldl (fun n r =>
    n+(if d == 23 || r.separate then rowCredit r k t else 0)) 0

def harmonicPass (rows : Array Row) (d k : Nat) (high t : Int) : Bool :=
  0 ≤ t && t ≤ thresholdScale &&
    (t == thresholdScale || targetPass d high (harmonicScore rows d k t))

def checkDegree (rows : Array Row) (sat : Array (Int × Int)) (d : Nat) : Bool :=
  let high := if d == 23 then 0 else nativeNumerator sat d
  let ts := thresholds d
  targetPass d high 0 ||
    (fejerPass d ts && (Array.ofFn fun k : Fin harmonics =>
      harmonicPass rows d k high (ts[k.val]?.getD 0)).all id)

def rowRange (arcs : Array Arc) (start count : Nat) : Array Row :=
  Array.ofFn fun (i : Fin count) => moments arcs (source (start+i))

def saturatedData (arcs : Array Arc) : Array (Int × Int) :=
  Array.ofFn fun (i : Fin 252) =>
    let s := saturated i
    (s.area,nativeFraction arcs s)

def checkData (rows : Array Row) (sat : Array (Int × Int)) : Bool :=
  (Array.ofFn fun i : Fin 5 => checkDegree rows sat (23+i.val)).all id &&
    targetPass 28 (nativeNumerator sat 28) 0

end HadwigerNelson.Stars.BoxCheck

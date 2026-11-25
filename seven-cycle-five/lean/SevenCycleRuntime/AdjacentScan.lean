import SevenCycleRuntime.Middle

namespace SevenCycle.Adjacent.Scan

open Contacts (Cube Index Height)

abbrev Marks := Vector Height 3
abbrev Visit := Cube → Cube → Marks → Marks → Cube → Bool
abbrev Contact := Height × Height

/-- Each transverse distance is checked in both physical orientations by
enumerating the later start. The cut lookup is shared by all three gaps. -/
def ordered (idx : Index) (s t : Cube) (a : Fin 3) : Array Contact :=
  let valid := Vector.ofFn (n := 7) fun j => idx.contains (Contacts.anchorKey s t a j)
  (#[1,2,3] : Array Height).flatMap fun gap =>
    ((Array.finRange 7).filter fun j => valid.get j && valid.get (j-gap)).map (fun j => (gap,j))

structure PairData where
  sites : Array Middle.Site
  common : Nat
  choices : Vector (Vector Middle.Choices 7) 3

/-- Materialize the 21 possible marked middle constraints once for a support
pair, then share their data across all gap orders and placements. -/
def prepare (idx : Index) (s t : Cube) : PairData :=
  let xs := Middle.sites s
  ⟨xs, Middle.flags xs (Middle.occupied t), Vector.ofFn fun a =>
    Vector.ofFn fun j => Middle.choices xs s t idx a j⟩

def checkPrepared (p : PairData) (gaps cs : Marks) (next : Cube → Bool) : Bool :=
  let wins := (Array.finRange 3).flatMap fun a =>
    #[(p.choices.get a).get (cs.get a - gaps.get a), (p.choices.get a).get (cs.get a)]
  Middle.join p.common p.sites.size (fun bits =>
    let u := Middle.materialize p.sites bits
    let n := Middle.count u
    n < 16 || 19 < n || next u) wins 0 0

def checkPair (idx : Index) (s t : Cube) (next : Visit) : Bool :=
  let xs := ordered idx s t 0
  xs.isEmpty ||
    let ys := ordered idx s t 1
    ys.isEmpty ||
      let zs := ordered idx s t 2
      zs.isEmpty ||
        let p := prepare idx s t
        xs.all fun x => ys.all fun y => zs.all fun z =>
          let gaps := #v[x.1,y.1,z.1]
          let cs := #v[x.2,y.2,z.2]
          checkPrepared p gaps cs (next s t gaps cs)

end SevenCycle.Adjacent.Scan

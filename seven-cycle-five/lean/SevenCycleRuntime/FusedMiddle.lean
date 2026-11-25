import SevenCycleRuntime.AdjacentScan

namespace SevenCycle.Adjacent.ScanFused

open Contacts (Cube Index Height)
open Scan (Marks Visit PairData)

abbrev Port := Fin 3 × Height

def ports (gaps cs : Marks) : Array Port :=
  (Array.finRange 3).flatMap fun a =>
    #[(a,cs.get a - gaps.get a), (a,cs.get a)]

abbrev walk := Middle.walkRows

def checked (p : PairData) (gaps cs : Marks) (gate leaf : Cube → Bool) : Bool :=
  let wins := (ports gaps cs).map fun (a,j) => (p.choices.get a).get j
  walk p.common (fun fixed selected =>
    let visible := Middle.materialize p.sites selected
    let maxBits := selected ||| (p.common ^^^ (p.common &&& fixed))
    19 < Middle.count visible || Middle.count (Middle.materialize p.sites maxBits) < 16 ||
      !gate visible ||
        Middle.join p.common p.sites.size (fun bits =>
          let u := Middle.materialize p.sites bits
          let n := Middle.count u
          n < 16 || 19 < n || leaf u) #[] fixed selected) wins 0 0

def checkPair (idx : Index) (s t : Cube) (gate leaf : Visit) : Bool :=
  let xs := Scan.ordered idx s t 0
  xs.isEmpty ||
    let ys := Scan.ordered idx s t 1
    ys.isEmpty ||
      let zs := Scan.ordered idx s t 2
      zs.isEmpty ||
        let p := Scan.prepare idx s t
        xs.all fun x => ys.all fun y => zs.all fun z =>
          let gaps := #v[x.1,y.1,z.1]
          let cs := #v[x.2,y.2,z.2]
          checked p gaps cs (gate s t gaps cs) (leaf s t gaps cs)

end SevenCycle.Adjacent.ScanFused

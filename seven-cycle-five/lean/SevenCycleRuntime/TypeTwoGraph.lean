import Init

/-! Perfect matching proposals in the 33-by-33 graph between two cube supports.
The subsequent checker validates a proposal before the matching bound is used. -/

namespace SevenCycle.TypeTwo.Graph

abbrev Site := Fin 343
abbrev Sites := Vector Site 33
abbrev Index := Fin 33
abbrev Cube := Vector UInt64 7

@[inline] def coord (p : Site) (a : Fin 3) : Fin 7 :=
  if a = 0 then Fin.ofNat 7 (p.val / 49)
  else if a = 1 then Fin.ofNat 7 (p.val / 7)
  else Fin.ofNat 7 p.val

@[inline] def close1 (a b : Fin 7) : Bool := a == b || a + 1 == b || b + 1 == a

@[inline] def near (x y : Site) : Bool :=
  close1 (coord x 0) (coord y 0) && close1 (coord x 1) (coord y 1) &&
    close1 (coord x 2) (coord y 2)

@[inline] def present (r : Cube) (x : Site) : Bool :=
  (r.get (coord x 0)).toNat.testBit (x.val % 49)

abbrev Matrix := Vector (BitVec 33) 33
abbrev Partial := Vector (Option Index) 33

private def maskOf (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => maskOf p n ||| (if p n then 2^n else 0)

def graph (S T : Sites) : Matrix :=
  Vector.ofFn fun i => BitVec.ofNat 33 (maskOf (fun j => near S[i] T[Fin.ofNat 33 j]) 33)

private def augment (g : Matrix) : Nat → Index → BitVec 33 → Partial → BitVec 33 × Option Partial
  | 0, _, visited, _ => (visited, none)
  | n+1, i, visited, mates => Id.run do
    let mut seen := visited
    for j in Array.finRange 33 do
      if g[i].getLsbD j && !seen.getLsbD j then
        seen := seen ||| ((1 : BitVec 33) <<< j.val)
        match mates[j] with
        | none => return (seen, some (mates.set j (some i)))
        | some other =>
          let (seen', next) := augment g n other seen mates
          seen := seen'
          if let some next := next then return (seen, some (next.set j (some i)))
    return (seen, none)

/-- Right sides index the returned pairs. A failed proposal leaves the layout
for the subsequent full cross-conflict test. -/
def propose (S T : Sites) : Option (Sites × Sites) := Id.run do
  let g := graph S T
  let mut mates : Partial := Vector.replicate 33 none
  for i in Array.finRange 33 do
    let (_, result) := augment g 33 i 0 mates
    let some next := result | return none
    mates := next
  return some (Vector.ofFn (fun j => S[mates[j].getD 0]), T)

/-- Equal points count as graph edges. Each side must have distinct vertices. -/
def valid (s t : Cube) (S T : Sites) : Bool :=
  (Array.finRange 33).all fun i =>
    present s S[i] && present t T[i] && near S[i] T[i] &&
      (Array.finRange 33).all fun j => i == j || (S[i] != S[j] && T[i] != T[j])

end SevenCycle.TypeTwo.Graph

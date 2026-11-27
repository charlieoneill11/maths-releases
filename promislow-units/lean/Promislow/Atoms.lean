import Promislow.Sparse

namespace Promislow

inductive Axis | x | y deriving DecidableEq, Repr

def tr (axis : Axis) (n : ℤ) : ElemP :=
  match axis with
  | .x => ⟨n,0,0,.e⟩
  | .y => ⟨0,n,0,.e⟩

def other : Axis → Axis | .x => .y | .y => .x

def screw : Axis → ElemP | .x => ElemP.genA | .y => ElemP.genB

inductive Letter | A | A' | B deriving DecidableEq, Repr

namespace Letter
def axis : Letter → Axis | .B => .y | _ => .x
def degree : Letter → ℕ | .A' => 2 | _ => 1
def spacing : Letter → ℤ | .B => 15 | _ => 3
end Letter

namespace Sparse

def series (a : Axis) (start : ℤ) (n : ℕ) : Poly :=
  (List.range n).map fun i => (tr a (start+i),1)

def factor (l : Letter) : Poly :=
  series l.axis (- (l.degree : ℤ)) (2*l.degree+1)

def phases : List (ℤ × ℤ) := [(-1,0),(1,-1),(-1,-2),(1,-1),(1,0),(-1,-1),(1,-2),(-1,-1)]

def elementary (l : Letter) (s : ℤ × ℤ) : Poly :=
  add (series l.axis 0 (l.degree+1))
    (mul (series l.axis 0 l.degree)
      (atom (tr (other l.axis) (l.spacing*s.2) * screw l.axis) s.1))

def atoms (l : Letter) (ss : List (ℤ × ℤ)) : Poly :=
  ss.foldl (fun acc s => mul acc (elementary l s)) one

def adjPhases (ss : List (ℤ × ℤ)) := ss.reverse.map (fun (s,j) => (-s,j))

def centered (l : Letter) (ss : List (ℤ × ℤ)) : Poly :=
  mul (atom (tr l.axis (-4*(l.degree:ℤ)))) (atoms l ss)

def num (l : Letter) (inv : Bool) : Poly :=
  centered l (if inv then adjPhases phases else phases)

def firstHalf (l : Letter) := atoms l (phases.take 4)
def prefixAdj (l : Letter) := centered l (adjPhases (phases.take 4))
def lastHalf (l : Letter) := centered l (phases.drop 4)
def suffixAdj (l : Letter) := atoms l (adjPhases (phases.drop 4))

end Sparse

noncomputable section
open Sparse

def F (l : Letter) := val (factor l)
def N (l : Letter) (inv : Bool) := val (num l inv)

end
end Promislow

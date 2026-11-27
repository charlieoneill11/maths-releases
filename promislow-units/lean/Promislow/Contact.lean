import Promislow.Letters

namespace Promislow

namespace Sparse

def scalarPart (l : Letter) (rev : Bool) : Poly :=
  (num l rev).filter fun t => decide (t.1.c = .e)

def screwPart (l : Letter) (rev : Bool) : Poly :=
  (num l rev).filter fun t => decide (t.1.c ≠ .e)

def minus (p : Poly) := p.map fun (g,c) => (g,-c)

/-- Propose a quotient by t^(-d)(1+...+t^(2d)) using the geometric series.
The equalities below independently check each proposed quotient by multiplication. -/
def divide (l : Letter) (p : Poly) : Poly := Id.run do
  let index := fun (g : ElemP) => if l.axis = .x then g.ix else g.iy
  let top := p.foldl (fun hi t => max hi (index t.1)) 0
  let mut result : Poly := []
  for (g,c) in p do
    let span := (top-index g).toNat
    for k in [:span / (2*l.degree+1)+1] do
      let n : ℤ := l.degree + k*(2*l.degree+1)
      if index g + n ≤ top - l.degree then
        result := insert (tr l.axis n * g) c result
      if index g + n+1 ≤ top - l.degree then
        result := insert (tr l.axis (n+1) * g) (-c) result
  return result

def scalarQuot (l f : Letter) (rev : Bool) : Poly :=
  divide f (add (scalarPart l rev) (minus (pow (factor l) 4)))

def screwQuot (l f : Letter) (rev : Bool) : Poly :=
  (divide f)^[5] (screwPart l rev)

end Sparse
open Sparse
noncomputable section

theorem transverse (l f : Letter) (rev : Bool) (h : l.axis ≠ f.axis) :
    N l rev = val (scalarPart l rev) + F f ^ 5 * val (screwQuot l f rev) ∧
    val (scalarPart l rev) = F l ^ 4 + F f * val (scalarQuot l f rev) := by
  unfold N F
  simp only [← val_mul,← val_add,← val_pow]
  constructor <;> apply congrArg val <;> cases l <;> cases f <;> cases rev <;>
    first | exact (h rfl).elim | native_decide

theorem transverse_commutes (l v : Letter) (rev : Bool) (h : l.axis ≠ v.axis) :
    Commute (val (scalarPart l rev)) (val (firstHalf v)) ∧
    Commute (val (scalarPart l rev)) (val (lastHalf v)) ∧
    Commute (val (scalarPart l rev)) (N v false) := by
  unfold Commute SemiconjBy N
  simp only [← val_mul]
  refine ⟨?_,?_,?_⟩ <;> apply congrArg val <;> cases l <;> cases v <;> cases rev <;>
    first | exact (h rfl).elim | native_decide

end
end Promislow

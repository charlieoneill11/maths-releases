import Std

/-! Fixed-point Gaussian arithmetic. The signed quotients truncate toward zero. -/

namespace HadwigerNelson.Arithmetic

structure GaussianInt where
  re : Int
  im : Int
deriving Inhabited, Repr, DecidableEq

namespace GaussianInt

/-- Floor both signed coordinates of a rational ray, as in the release's ray table. -/
def ofRay (S x y den : Int) : GaussianInt := ⟨(S*x)/den,(S*y)/den⟩

def mul (S : Int) (a b : GaussianInt) : GaussianInt where
  re := (a.re*b.re-a.im*b.im).tdiv S
  im := (a.re*b.im+a.im*b.re).tdiv S

def power (S : Int) (base : GaussianInt) : Nat → GaussianInt
  | 0 => ⟨S,0⟩
  | k+1 => (power S base k).mul S base

private def tableState (S : Int) (base : GaussianInt) : Nat → GaussianInt × Array GaussianInt
  | 0 => (⟨S,0⟩,#[])
  | k+1 =>
    let (last, entries) := tableState S base k
    let next := mul S last base
    (next, entries.push next)

/-- Entry k contains the harmonic k+1. A full table uses one multiplication per harmonic. -/
def powerTable (S : Int) (base : GaussianInt) (count : Nat) : Array GaussianInt :=
  (tableState S base count).2

private theorem tableState_spec (S : Int) (base : GaussianInt) (n : Nat) :
    (tableState S base n).1 = power S base n ∧ (tableState S base n).2.size = n ∧
    ∀ k < n, (tableState S base n).2[k]? = some (power S base (k+1)) := by
  induction n with
  | zero => simp [tableState,power]
  | succ n ih =>
    obtain ⟨hl,hs,hi⟩ := ih
    refine ⟨?_,?_,?_⟩
    · simp [tableState,power,hl]
    · simp [tableState,hs]
    · intro k hk
      rw [tableState]
      simp only [Array.getElem?_push,hs]
      split
      · rename_i he
        subst k
        simp [power,hl]
      · exact hi k (by omega)

theorem powerTable_size (S : Int) (base : GaussianInt) (count : Nat) :
    (powerTable S base count).size = count := (tableState_spec S base count).2.1

theorem powerTable_get (S : Int) (base : GaussianInt) (count k : Nat) (hk : k < count) :
    (powerTable S base count)[k]? = some (power S base (k+1)) :=
  (tableState_spec S base count).2.2 k hk

end GaussianInt
end HadwigerNelson.Arithmetic

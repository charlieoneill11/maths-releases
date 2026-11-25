import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Counting one or two prescribed independent choices in the halving experiment. -/

namespace HadwigerNelson.Crossings

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem fair_fixed (s : Finset ι) (values : ι → Bool) :
    2^s.card * (Finset.univ.filter (fun ω : ι → Bool => ∀ i ∈ s, ω i = values i)).card =
      Fintype.card (ι → Bool) := by
  classical
  let choices (i : ι) : Finset Bool := if i ∈ s then {values i} else Finset.univ
  have assignments : Finset.univ.filter (fun ω : ι → Bool => ∀ i ∈ s, ω i = values i)
      = Fintype.piFinset choices := by
    ext ω
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : i ∈ s <;> simp [choices,hi,h i]
    · intro h i hi
      simpa [choices,hi] using h i
  have factor : (∏ i : ι, if i ∈ s then 2 else (1:Nat)) = 2^s.card := by
    rw [Finset.prod_ite]
    simp
  rw [assignments,Fintype.card_piFinset,←factor,←Finset.prod_mul_distrib,Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [choices,hi,Fintype.card_bool]

theorem fair_one (i : ι) (a : Bool) :
    2 * (Finset.univ.filter (fun ω : ι → Bool => ω i = a)).card = Fintype.card (ι → Bool) := by
  simpa using fair_fixed ({i} : Finset ι) (fun _ => a)

theorem fair_two (i j : ι) (hij : i ≠ j) (a b : Bool) :
    4 * (Finset.univ.filter (fun ω : ι → Bool => ω i = a ∧ ω j = b)).card =
      Fintype.card (ι → Bool) := by
  simpa [hij,hij.symm] using fair_fixed ({i,j} : Finset ι) (fun x => if x=i then a else b)

end HadwigerNelson.Crossings

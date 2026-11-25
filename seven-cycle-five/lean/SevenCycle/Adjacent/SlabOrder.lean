import SevenCycle.Adjacent.SlabTables

namespace SevenCycle.Adjacent.SlabTables
open SlabJoin

private theorem enumerate (g : Gaps) : #v[g.get 0,g.get 1,g.get 2] = g := by
  apply Vector.ext
  intro i hi
  have cases : i=0 ∨ i=1 ∨ i=2 := by omega
  rcases cases with rfl|rfl|rfl <;> rfl

theorem order_injective (g : Gaps) : Function.Injective (fun i : Fin 4 => (orderToCanonical g)[i]) := by
  have all : ∀ a b c : Fin 7, ∀ (i j : Fin 4),
    (orderToCanonical #v[a,b,c])[i] = (orderToCanonical #v[a,b,c])[j] → i=j := by decide +kernel
  rw [← enumerate g]
  exact all _ _ _

noncomputable def rankPerm (g : Gaps) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective _ ((Finite.injective_iff_bijective).mp (order_injective g))

theorem order_apply (g : Gaps) (j : Fin 4) : (orderToCanonical g)[j] = rankPerm g j := rfl

theorem rank_zero (g : Gaps) : rankPerm g 0 = 0 := rfl

def sortedProfile (g : Gaps) : Vector (Fin 7) 4 :=
  let a := g.get 0
  let b := g.get 1
  let c := g.get 2
  #v[1,min a (min b c),max (min a b) (min c (max a b)),max a (max b c)]

theorem sorted_at (g : Gaps) (j : Fin 4) :
    (sortedProfile g).get (rankPerm g j) = Fin.cons (α := fun _ => Fin 7) 1 g.get j := by
  have all : ∀ a b c : Fin 7, ∀ i : Fin 4,
      (sortedProfile #v[a,b,c]).get ((orderToCanonical #v[a,b,c])[i]) =
        Fin.cons (α := fun _ => Fin 7) 1 (#v[a,b,c] : Gaps).get i := by decide +kernel
  rw [← enumerate g]
  exact all _ _ _ _

end SevenCycle.Adjacent.SlabTables

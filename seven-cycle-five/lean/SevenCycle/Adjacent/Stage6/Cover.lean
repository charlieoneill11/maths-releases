import SevenCycle.Adjacent.Exterior
import SevenCycle.Adjacent.SlabJoin

/-! A checked branching bound on the number of additional words in a marked band. -/

namespace SevenCycle.Adjacent.Stage6

open Blueprint Proof

/-- Indices are base-seven addresses in the physical four-dimensional box.
A split considers both possible decisions for a site. -/
inductive Tree where
  | boxes (corners : Array Nat)
  | split (site : Nat) (present absent : Tree)

def near (x y : Tuple 4) : Bool :=
  (Array.finRange 4).all fun k => let d := x k - y k; d == -1 || d == 0 || d == 1

theorem near_iff (x y : Tuple 4) : near x y = true ↔ ∀ k, cycleStep (x k) (y k) := by
  simp only [near, Array.all_eq_true', Bool.or_eq_true_iff, beq_iff_eq]
  constructor
  · intro h k
    have hv := h k (Array.mem_ofFn.mpr ⟨k,rfl⟩)
    simpa [cycleStep, or_assoc] using hv
  · intro h k _
    simpa [cycleStep, or_assoc] using h k

/-- Every terminal node verifies that its available sites are contained in
fewer unit boxes than the number still needed. -/
def checkTree : Tree → Array (Tuple 4) → Nat → Bool
  | .boxes qs, xs, need => qs.size < need && xs.all (fun x => qs.any fun q => Exterior.inBox (SlabJoin.position q) x)
  | .split v yes no, xs, need =>
    let z := SlabJoin.position v
    checkTree yes (xs.filter fun x => !near x z) (need-1) &&
      checkTree no (xs.filter fun x => x != z) need

theorem checkTree_sound (t : Tree) (pool : Array (Tuple 4)) (need : Nat)
    (ok : checkTree t pool need = true) (X : Finset (Tuple 4)) (hc : packing cycleStep X)
    (sub : ∀ x ∈ X, x ∈ pool) : X.card < need := by
  induction t generalizing pool need X with
  | boxes qs =>
    obtain ⟨hlen,hcover⟩ := Bool.and_eq_true_iff.mp ok
    have len : qs.size < need := of_decide_eq_true hlen
    have cover (x : X) : ∃ i : Fin qs.size, Exterior.inBox (SlabJoin.position qs[i]) x.val := by
      have h := Array.all_eq_true'.mp hcover x (sub x x.property)
      obtain ⟨q,hq,hinside⟩ := Array.any_eq_true'.mp h
      obtain ⟨i,hi,rfl⟩ := Array.mem_iff_getElem.mp hq
      exact ⟨⟨i,hi⟩,hinside⟩
    choose f hf using cover
    have inj : Function.Injective f := by
      intro x y eq
      apply Subtype.ext
      by_contra hne
      exact hc x x.property y y.property ⟨hne, Exterior.box_near (hf x) (eq ▸ hf y)⟩
    have h := Fintype.card_le_of_injective f inj
    simp only [Fintype.card_coe, Fintype.card_fin] at h
    omega
  | split v yes no iy ino =>
    obtain ⟨hy,hn⟩ := Bool.and_eq_true_iff.mp ok
    let z := SlabJoin.position v
    by_cases hz : z ∈ X
    · have h := iy _ _ hy (X.erase z)
        (fun x hx y hy => hc x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy))
        (by
          intro x hx
          obtain ⟨hne,hx'⟩ := Finset.mem_erase.mp hx
          apply Array.mem_filter.mpr
          refine ⟨sub _ hx', ?_⟩
          have hfar : near x (SlabJoin.position v) = false := Bool.eq_false_iff.mpr (fun e => hc x hx' z hz ⟨hne, (near_iff ..).mp e⟩)
          simp [hfar])
      rw [Finset.card_erase_of_mem hz] at h
      have pos := Finset.card_pos.mpr ⟨_,hz⟩
      omega
    · apply ino _ _ hn X hc
      intro x hx
      exact Array.mem_filter.mpr ⟨sub _ hx, bne_iff_ne.mpr (fun e => hz (by simpa only [z, ← e] using hx))⟩

end SevenCycle.Adjacent.Stage6

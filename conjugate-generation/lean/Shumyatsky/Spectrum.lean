import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Nat.Prime.Basic

namespace Shumyatsky

universe u
variable {G Q : Type*} [Group G] [Group Q]

def spectrum (G : Type*) : Set ℕ := {p | p.Prime ∧ p ∣ Nat.card G}

def pair (x g : G) : Subgroup G := Subgroup.closure {x, g * x * g⁻¹}

def Captures (G : Type*) [Group G] : Prop := ∃ x g : G, spectrum (pair x g) = spectrum G

def Minimal (G : Type*) [Group G] : Prop := ∀ H : Subgroup G, spectrum H = spectrum G → H = ⊤

theorem spectrum_mono {A B : Type*} (h : Nat.card A ∣ Nat.card B) :
    spectrum A ⊆ spectrum B := fun _ hp => ⟨hp.1, hp.2.trans h⟩

theorem spectrum_eq_of_card_eq {A B : Type*} (h : Nat.card A = Nat.card B) :
    spectrum A = spectrum B := by simp only [spectrum, h]

theorem pair_map (f : G →* Q) (x g : G) : (pair x g).map f = pair (f x) (f g) := by
  simp [pair, MonoidHom.map_closure, Set.image_pair]

theorem minimal_of_surjective (hG : Minimal G) (f : G →* Q) (hf : Function.Surjective f) :
    Minimal Q := by
  intro U hU
  let V := U.comap f
  have hmap : V.map f = U := Subgroup.map_comap_eq_self_of_surjective hf _
  have hker : f.ker ≤ V := by
    intro x hx
    show f x ∈ U
    rw [MonoidHom.mem_ker.mp hx]
    exact U.one_mem
  have hord : Nat.card G = Nat.card Q * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  have hV : V = ⊤ := hG V (Set.Subset.antisymm (spectrum_mono V.card_subgroup_dvd_card) (by
    rintro p ⟨hp, hd⟩
    rw [hord] at hd
    rcases hp.dvd_mul.mp hd with h | h
    · have hu : p ∈ spectrum U := hU.symm ▸ (show p ∈ spectrum Q from ⟨hp, h⟩)
      exact ⟨hp, hu.2.trans (hmap ▸ Subgroup.card_map_dvd V f)⟩
    · exact ⟨hp, h.trans (Subgroup.card_dvd_of_le hker)⟩))
  rw [← hmap, hV, Subgroup.map_top_of_surjective _ hf]

/-- Choose a subgroup of minimum cardinality among all those with full spectrum. -/
theorem exists_minimal [Finite G] : ∃ P : Subgroup G, Minimal P ∧ spectrum P = spectrum G := by
  classical
  let good (n : ℕ) := ∃ P : Subgroup G, Nat.card P = n ∧ spectrum P = spectrum G
  have hex : ∃ n, good n := ⟨_, ⊤, rfl, spectrum_eq_of_card_eq Subgroup.card_top⟩
  obtain ⟨P, hcard, hspec⟩ := Nat.find_spec hex
  refine ⟨P, ?_, hspec⟩
  intro K hK
  let U := K.map P.subtype
  have he : Nat.card K = Nat.card U :=
    Nat.card_congr (K.equivMapOfInjective P.subtype Subtype.val_injective).toEquiv
  have hle := Nat.find_min' hex (show good (Nat.card K) from
    ⟨U, he.symm, (spectrum_eq_of_card_eq he.symm).trans (hK.trans hspec)⟩)
  apply K.eq_top_of_card_eq
  exact Nat.le_antisymm (Nat.le_of_dvd Nat.card_pos K.card_subgroup_dvd_card) (hcard ▸ hle)

theorem captures_of_minimal_subgroups [Finite G]
    (all : ∀ P : Subgroup G, Minimal P → ∃ x g : P, pair x g = ⊤) : Captures G := by
  obtain ⟨P, hmin, hspec⟩ := exists_minimal (G := G)
  obtain ⟨x, g, h⟩ := all P hmin
  refine ⟨x.val, g.val, ?_⟩
  have he : Nat.card (pair (G := P) x g) = Nat.card (pair x.val g.val) := by
    change Nat.card (pair x g) = Nat.card (pair (P.subtype x) (P.subtype g))
    rw [← pair_map P.subtype]
    exact Nat.card_congr ((pair x g).equivMapOfInjective _ Subtype.val_injective).toEquiv
  exact (spectrum_eq_of_card_eq he.symm).trans
    ((spectrum_eq_of_card_eq (h ▸ Subgroup.card_top)).trans hspec)

theorem reduction :
    (∀ (G : Type u) [Group G] [Finite G], Captures G) ↔
    (∀ (G : Type u) [Group G] [Finite G], Minimal G → ∃ x g : G, pair x g = ⊤) := by
  constructor
  · intro all G _ _ hG
    obtain ⟨x, g, h⟩ := all G
    exact ⟨x, g, hG _ h⟩
  · intro all G _ _
    exact captures_of_minimal_subgroups (fun P => all P)

/-- The image of a subgroup of H on a stabilized factor supplies primes of H. -/
theorem spectrum_of_section (H : Subgroup G) (K : Subgroup H) (f : K →* Q)
    (S : Subgroup Q) (hS : S ≤ f.range) : spectrum S ⊆ spectrum H :=
  spectrum_mono ((Subgroup.card_dvd_of_le hS).trans
    ((Subgroup.card_range_dvd f).trans K.card_subgroup_dvd_card))

end Shumyatsky

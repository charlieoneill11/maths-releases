import Shumyatsky.Induction
import Mathlib.GroupTheory.SchurZassenhaus

namespace Shumyatsky
open Subgroup

/-- The only property of the soluble Hall theorem used on the outer quotient:
a subgroup of order prime to the socle contains all the primes outside it. -/
theorem outer_coprime {L Q : Type*} [Group L] [Group Q] [Finite L] [Finite Q]
    (hL : Minimal L) (f : L →* Q) (hf : Function.Surjective f)
    (D : Subgroup Q) (hD : (Nat.card f.ker).Coprime (Nat.card D))
    (outside : ∀ p ∈ spectrum Q, p ∉ spectrum f.ker → p ∈ spectrum D) :
    (Nat.card f.ker).Coprime (Nat.card Q) := by
  let V := D.comap f
  have hmap : V.map f = D := Subgroup.map_comap_eq_self_of_surjective hf _
  have hker : f.ker ≤ V := fun x hx => by
    change f x ∈ D
    rw [MonoidHom.mem_ker.mp hx]
    exact D.one_mem
  have hV : V = ⊤ := hL V (Set.Subset.antisymm (spectrum_mono V.card_subgroup_dvd_card) (by
    intro p hp
    by_cases hk : p ∈ spectrum f.ker
    · exact spectrum_mono (Subgroup.card_dvd_of_le hker) hk
    · have hd := hp.2
      rw [card_eq_card_quotient_mul_card_subgroup f.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at hd
      have hq : p ∈ spectrum Q := ⟨hp.1, (hp.1.dvd_mul.mp hd).resolve_right (fun h => hk ⟨hp.1,h⟩)⟩
      exact spectrum_mono (hmap ▸ Subgroup.card_map_dvd V f) (outside _ hq hk)))
  have htop : D = ⊤ := by rw [← hmap, hV, Subgroup.map_top_of_surjective f hf]
  simpa [htop] using hD

/-- For the single-factor block, rho is the action on the simple group, L is
its image, and f is the cyclic outer quotient. -/
theorem single_step {G L Q : Type*} [Group G] [Group L] [CommGroup Q] [Finite L] [Finite Q]
    (hG : Minimal G) (N : Subgroup G) [N.Normal] (ρ : G →* L) (hρ : Function.Surjective ρ)
    (f : L →* Q) (hf : Function.Surjective f) (hN : N.map ρ = f.ker)
    (inj : Function.Injective (ρ.comp N.subtype))
    (generators : ∃ a b : L, pair a b = ⊤) (x₀ g₀ : G)
    (quot : pair (QuotientGroup.mk' N x₀) (QuotientGroup.mk' N g₀) = ⊤) :
    ∃ x g : G, pair x g = ⊤ := by
  let p := QuotientGroup.mk' N
  let t := f.comp ρ
  have factors : N ≤ t.ker := by
    intro n hn
    change ρ n ∈ f.ker
    rw [← hN]
    exact ⟨n,hn,rfl⟩
  let φ := QuotientGroup.lift N t factors
  have onto : Function.Surjective φ := by
    intro y
    obtain ⟨w,rfl⟩ := hf.comp hρ y
    exact ⟨p w,rfl⟩
  obtain ⟨a,b,hab⟩ := generators
  have hc : zpowers (t x₀) = ⊤ := image_generator φ onto quot
  obtain ⟨x,g,hx,hg,hpair⟩ := prescribe_cosets f hf (t x₀) (t g₀) hc hab
  have realize (z : L) (z₀ : G) (hz : f z = t z₀) :
      ∃ w : G, p w = p z₀ ∧ ρ w = z := by
    have hk : (ρ z₀)⁻¹ * z ∈ f.ker := by simp [MonoidHom.mem_ker,hz,t]
    obtain ⟨n,hn,he⟩ := hN.symm ▸ hk
    exact ⟨z₀*n, by simpa [p] using hn, by simp [he]⟩
  obtain ⟨w,hw,hw'⟩ := realize x x₀ hx
  obtain ⟨k,hk,hk'⟩ := realize g g₀ hg
  have hm : (pair w k).map ρ = ⊤ := by rw [pair_map,hw',hk',hpair]
  have hd : Nat.card L ∣ Nat.card (pair w k) := by
    simpa [hm] using Subgroup.card_map_dvd (pair w k) ρ
  exact ⟨w,k,finish_normal hG N _ (quotient_pair_surj N w k (by
    change pair (p w) (p k) = ⊤; rwa [hw,hk]))
    (spectrum_mono ((Subgroup.card_dvd_of_injective _ inj).trans hd))⟩

end Shumyatsky

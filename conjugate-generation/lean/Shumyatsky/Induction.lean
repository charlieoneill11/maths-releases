import Shumyatsky.FactorAction
import Shumyatsky.Cyclic

namespace Shumyatsky
open Subgroup

variable {G : Type*} [Group G]

theorem quotient_pair_surj (N : Subgroup G) [N.Normal] (x g : G)
    (h : pair (QuotientGroup.mk' N x) (QuotientGroup.mk' N g) = ⊤) :
    Function.Surjective ((QuotientGroup.mk' N).comp (pair x g).subtype) := by
  apply MonoidHom.range_eq_top.mp
  rw [MonoidHom.range_comp, Subgroup.range_subtype, pair_map, h]

/-- If H generates modulo N and already accounts for the primes of N, then it
has the full prime spectrum. -/
theorem finish_normal (hG : Minimal G) (N : Subgroup G) [N.Normal] (H : Subgroup G)
    (onto : Function.Surjective ((QuotientGroup.mk' N).comp H.subtype))
    (kernelPrimes : spectrum N ⊆ spectrum H) : H = ⊤ := by
  apply hG H (Set.Subset.antisymm (spectrum_mono H.card_subgroup_dvd_card) ?_)
  rintro p ⟨hp, hd⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N] at hd
  rcases hp.dvd_mul.mp hd with h | h
  · exact ⟨hp, h.trans (Subgroup.card_dvd_of_surjective _ onto)⟩
  · exact kernelPrimes ⟨hp,h⟩

/-- Use the strong induction hypothesis on a proper quotient, also when
the quotient is trivial. -/
theorem induction_on_normal_in
    (C : ∀ (T : Type u) [Group T], Prop)
    (sub : ∀ (T : Type u) [Group T] (H : Subgroup T), C T → C H)
    (quot : ∀ (T : Type u) [Group T] (N : Subgroup T) [N.Normal], C T → C (T ⧸ N))
    (lift : ∀ (G : Type u) [Group G] [Finite G] [Nontrivial G], C G → Minimal G →
      ∃ (N : Subgroup G) (_ : N.Normal), N ≠ ⊥ ∧
        ∀ x g : G, pair (QuotientGroup.mk' N x) (QuotientGroup.mk' N g) = ⊤ →
          ∃ a b : G, pair a b = ⊤)
    (G : Type u) [Group G] [Finite G] (hCG : C G) : Captures G := by
  apply captures_of_minimal_subgroups
  intro F hF
  suffices aux : ∀ n (T : Type u) [Group T] [Finite T], Nat.card T = n →
      C T → Minimal T → ∃ x g : T, pair x g = ⊤ from aux _ F rfl (sub G F hCG) hF
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T _ _ hc hCT hm
    cases subsingleton_or_nontrivial T with
    | inl h => exact ⟨1,1,Subsingleton.elim _ _⟩
    | inr ht =>
      obtain ⟨N,hN,hne,step⟩ := lift T hCT hm
      letI := hN
      have hlt : Nat.card (T ⧸ N) < n := by
        rw [← hc, card_eq_card_quotient_mul_card_subgroup N]
        exact lt_mul_of_one_lt_right Nat.card_pos ((one_lt_card_iff_ne_bot N).mpr hne)
      obtain ⟨x,g,h⟩ := ih _ hlt (T ⧸ N) rfl (quot T N hCT)
        (minimal_of_surjective hm _ (QuotientGroup.mk'_surjective N))
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N x
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective N g
      exact step x g h

theorem induction_on_normal
    (lift : ∀ (G : Type u) [Group G] [Finite G] [Nontrivial G], Minimal G →
      ∃ (N : Subgroup G) (_ : N.Normal), N ≠ ⊥ ∧
        ∀ x g : G, pair (QuotientGroup.mk' N x) (QuotientGroup.mk' N g) = ⊤ →
          ∃ a b : G, pair a b = ⊤)
    (G : Type u) [Group G] [Finite G] : Captures G :=
  induction_on_normal_in (fun _ _ => True) (fun _ _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun T _ _ _ _ => lift T) G trivial

section Block
open Labelled
variable {ι A O : Type*} [Finite ι] [Nontrivial ι] [Group A] [Group O]
variable (N : Subgroup G) [N.Normal] (ρ : G →* Labelled ι A) (q : A →* O)

omit [Finite ι] [Nontrivial ι] in
/-- Derive joint transitivity from transitivity of G, triviality of the
kernel permutation and quotient generation. -/
theorem quotient_transitivity (x g : G)
    (onto : Function.Surjective ((QuotientGroup.mk' N).comp (pair x g).subtype))
    (trans : ∀ i j, ∃ h : G, (ρ h).perm i = j)
    (trivialPerm : ∀ n : N, (ρ n).perm = 1) :
    Walk.connectedBy (ρ x).perm (ρ (g*x*g⁻¹)).perm := by
  intro r hx hy i j
  let good : Subgroup G := {
    carrier := {h | ∀ i, r.r i ((ρ h).perm i)}
    one_mem' := by intro k; rw [map_one]; exact r.iseqv.refl k
    mul_mem' := fun {h k} hh hk i => by rw [map_mul, mul_perm]; exact r.trans (hk i) (hh _)
    inv_mem' := fun {h} hh i => by
      rw [map_inv]
      change r.r i ((ρ h).perm.symm i)
      have he := hh ((ρ h).perm.symm i)
      rw [(ρ h).perm.apply_symm_apply] at he
      exact r.symm he }
  have hsub : pair x g ≤ good := by
    rw [pair, Subgroup.closure_le]
    intro s hs
    rcases Set.mem_insert_iff.mp hs with h | h
    · exact h ▸ hx
    · exact Set.mem_singleton_iff.mp h ▸ hy
  obtain ⟨h,he⟩ := trans i j
  obtain ⟨w,hw⟩ := onto (QuotientGroup.mk' N h)
  have hn : w.val⁻¹ * h ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N _ = 1
    rw [map_mul, map_inv, show QuotientGroup.mk' N w.val = _ from hw, inv_mul_cancel]
  have hg : w.val⁻¹ * h ∈ good := fun k => by
    rw [show (ρ (w.val⁻¹ * h)).perm = 1 from trivialPerm ⟨_,hn⟩]
    exact r.refl k
  have hh : h ∈ good := by simpa using good.mul_mem (hsub w.property) hg
  exact he ▸ hh i

/-- Lift two actions on one nonsingleton normal block to elements of G.
The base-image hypothesis identifies the kernel corrections available in N. -/
theorem block_step (hG : Minimal G) (x₀ g₀ : G)
    (quot : pair (QuotientGroup.mk' N x₀) (QuotientGroup.mk' N g₀) = ⊤)
    (trans : ∀ i j, ∃ h : G, (ρ h).perm i = j) (trivialPerm : ∀ n : N, (ρ n).perm = 1)
    (baseImage : ∀ b : ι → q.ker, ∃ n : N, ρ n = base (fun i => (b i : A)))
    (two : Block.CanLiftTwo q) (hSpec : spectrum N ⊆ spectrum q.ker) :
    ∃ x g : G, pair x g = ⊤ := by
  classical
  let X := ρ x₀
  let C := ρ g₀
  let Y := ρ (g₀*x₀*g₀⁻¹)
  have conj : C * X = Y * C := by simp [X,Y,C,mul_assoc]
  have perm := fun i => congrArg (fun z : Labelled ι A => z.perm i) conj
  have baseEq := fun i => congrArg (fun z : Labelled ι A => z.label i) conj
  let r : ι := Classical.arbitrary ι
  obtain ⟨x,y,g,hx,hg,eqn,loops⟩ := Block.lift X.perm Y.perm C.perm perm
    (quotient_transitivity N ρ x₀ g₀ (quotient_pair_surj N _ _ quot) trans trivialPerm)
    q two X.label Y.label C.label baseEq r
  have realize (z₀ : G) (l : ι → A) (h : ∀ i, q (l i) = q ((ρ z₀).label i)) :
      ∃ z : G, QuotientGroup.mk' N z = QuotientGroup.mk' N z₀ ∧
        ρ z = ⟨(ρ z₀).perm,l⟩ := by
    obtain ⟨b,hb⟩ := (same_coset q (ρ z₀) ⟨(ρ z₀).perm,l⟩).mp ⟨rfl,fun i => (h i).symm⟩
    obtain ⟨n,hn⟩ := baseImage b
    exact ⟨z₀*n, by simp [n.property], by rwa [map_mul, hn]⟩
  obtain ⟨a,ha,hA⟩ := realize x₀ x hx
  obtain ⟨c,hc,hC⟩ := realize g₀ g hg
  have hY : ρ (c*a*c⁻¹) = ⟨Y.perm,y⟩ := by
    rw [map_mul,map_mul,map_inv,hA,hC]
    apply (mul_inv_eq_iff_eq_mul).2
    exact extensionality (Equiv.ext perm) eqn
  refine ⟨a,c,finish_normal hG N _ (quotient_pair_surj N _ _ (by rwa [ha,hc])) (hSpec.trans ?_)⟩
  apply spectrum_mono ((Subgroup.card_dvd_of_le loops).trans ?_)
  simpa only [hA,hY] using loops_card_dvd ρ a c r

end Block
end Shumyatsky

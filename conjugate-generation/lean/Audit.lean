import Shumyatsky

open Shumyatsky

-- Spell out the question at the public boundary. The generator and conjugator are
-- chosen once, before quantifying over the primes.
example (facts : Inputs.{u}) (G : Type u) [Group G] [Finite G] :
    ∃ x g : G, ∀ p : ℕ, p.Prime →
      (p ∣ Nat.card (Subgroup.closure {x, g*x*g⁻¹}) ↔ p ∣ Nat.card G) := by
  obtain ⟨x,g,h⟩ := shumyatsky_of_inputs facts G
  refine ⟨x,g,fun p hp => ?_⟩
  have eqp := Set.ext_iff.mp h p
  simpa [spectrum,pair,hp] using eqp

/-- info: 'Shumyatsky.shumyatsky_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shumyatsky.shumyatsky_of_inputs

/-- info: 'Shumyatsky.shumyatsky_solvable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shumyatsky.shumyatsky_solvable

/-- info: 'Shumyatsky.Block.lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shumyatsky.Block.lift

/-- info: 'Shumyatsky.realize_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Shumyatsky.realize_pair

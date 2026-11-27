import Promislow.Descent
import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.Algebra.Group.Commute.Units

namespace Promislow

noncomputable section
universe u v
variable {R : Type u} {S : Type v} [Ring R] [Ring S]

/-- Elements for which some power of the given central element clears the denominator. -/
def over (ι : R →+* S) (d : S) (cd : ∀ z, Commute d z) (hd : d ∈ ι.range) : Subring S where
  carrier := {x | ∃ n : ℕ, d^n*x ∈ ι.range}
  one_mem' := ⟨0, by simp⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by rintro x ⟨n,hn⟩; exact ⟨n, by simpa using ι.range.neg_mem hn⟩
  add_mem' := by
    rintro x y ⟨i,hi⟩ ⟨j,hj⟩
    refine ⟨i+j, ?_⟩
    rw [mul_add]
    apply ι.range.add_mem
    · rw [Nat.add_comm,pow_add,mul_assoc]
      exact ι.range.mul_mem (ι.range.pow_mem hd j) hi
    · rw [pow_add,mul_assoc]
      exact ι.range.mul_mem (ι.range.pow_mem hd i) hj
  mul_mem' := by
    rintro x y ⟨i,hi⟩ ⟨j,hj⟩
    refine ⟨i+j, ?_⟩
    simpa only [pow_add,mul_assoc, ((cd x).pow_left j).left_comm] using ι.range.mul_mem hi hj

theorem over_base (ι : R →+* S) {d : S} {cd hd} (r : R) : ι r ∈ over ι d cd hd :=
  ⟨0, by simp⟩

/-- Inverting a central regular denominator gives a faithful ring extension. -/
theorem exists_extension (d : R) (cd : ∀ a, Commute d a)
    (reg : ∀ r, d*r=0 → r=0) :
    ∃ (S : Type u) (_ : Ring S) (ι : R →+* S), Function.Injective ι ∧ IsUnit (ι d) ∧
      ∀ f : R, (∀ a, Commute f a) → ∀ s : S, Commute (ι f) s := by
  let M := Submonoid.powers d
  have cM (s : M) (a : R) : Commute (s:R) a := by
    obtain ⟨n,hn⟩ := s.2
    rw [← hn]
    exact (cd a).pow_left n
  letI : OreLocalization.OreSet M := {
    oreNum := fun r _ => r
    oreDenom := fun _ s => s
    ore_eq := fun r s => (cM s r).eq
    ore_right_cancel := fun r t s h => ⟨s, (cM s r).eq.trans (h.trans (cM s t).eq.symm)⟩ }
  let A := OreLocalization M R
  let ι : R →+* A := OreLocalization.numeratorRingHom
  refine ⟨A,inferInstance,ι,OreLocalization.numeratorHom_inj ?_, ?_, ?_⟩
  · rintro a ⟨n,rfl⟩ r h
    induction n generalizing r with
    | zero => simpa using h
    | succ n ih =>
      change d^(n+1)*r=0 at h
      rw [pow_succ',mul_assoc] at h
      exact ih _ (reg _ h)
  · exact OreLocalization.numerator_isUnit (⟨d,1, pow_one _⟩ : M)
  · intro f cf s
    induction s using OreLocalization.ind with
    | _ r den =>
      let v : Aˣ := (OreLocalization.numerator_isUnit den).unit
      have hv : (v:A) = ι den := IsUnit.unit_spec _
      have hr : Commute (ι f) (ι r) := (cf r).map ι
      have hv' : Commute (ι f) (v:A) := hv ▸ (cf (den:R)).map ι
      have hs : (v:A) * OreLocalization.oreDiv r den = ι r := by
        rw [hv]; exact OreLocalization.mul_cancel
      have ht := congrArg (fun x : A => (↑v⁻¹:A)*x) hs
      simp only [← mul_assoc, Units.inv_mul, one_mul] at ht
      rw [ht]
      exact hv'.units_inv_right.mul_right hr

end
end Promislow

import Promislow.Binary
import Promislow.Presentation

namespace Promislow
noncomputable section
open MonoidAlgebra

theorem Ambient.eval_whole {S : Type*} [Ring S] (E : Ambient S) : E.eval whole=E.solution := by
  simp only [whole,wa,wb,E.eval_comm]
  change deepWord (commWord _ _) (commWord _ _) = _
  simp [Ambient.solution,Ambient.W,Ambient.eval,Ambient.signed]

/-- The integral witnesses are the two words in the given cyclotomic units.
The first product equation records which particular integral element is obtained. -/
theorem integral_certificate :
    ∃ u v : MonoidAlgebra ℤ ElemP,
      wordD whole * u = wordN whole ∧ u*v=1 ∧ v*u=1 ∧
      ∀ g : ElemP, u ≠ single g 1 ∧ u ≠ -single g 1 := by
  obtain ⟨S,i,⟨E⟩⟩ := Ambient.exists_ambient
  obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := E.solution_integral
  have eqn : wordD whole*u=wordN whole := E.inj (by
    rw [map_mul,hu,← E.eval_whole,E.cleared])
  refine ⟨u,v,eqn,E.inj ?_,E.inj ?_,Image.not_signed u eqn⟩
  · rw [map_mul,hu,hv,Units.mul_inv,map_one]
  · rw [map_mul,hu,hv,Units.inv_mul,map_one]

/-- Every cleared denominator acts injectively, so its numerator equation
determines at most one element of the integral group ring. -/
theorem wordD_regular (w : Word) : IsLeftRegular (wordD w) := by
  induction w with
  | nil => change IsLeftRegular (1 : IntegralGroupRing); intro p q h; simpa using h
  | cons t ws ih =>
    obtain ⟨l,r⟩ := t
    have reg : IsLeftRegular (F l) := by
      intro a b h
      change F l * a = F l * b at h
      exact sub_eq_zero.mp (regularF l (a-b) (by rw [mul_sub,h,sub_self]))
    exact (reg.pow 4).mul ih

/-- Both numerator equations refer literally to the arrays read from integral-pair.json. -/
theorem recorded_certificate :
    ∃ u v : MonoidAlgebra ℤ ElemP,
      wordD recordedU * u = wordN recordedU ∧ wordD recordedV * v = wordN recordedV ∧
      u*v=1 ∧ v*u=1 ∧ ∀ g : ElemP, u ≠ single g 1 ∧ u ≠ -single g 1 := by
  obtain ⟨S,i,⟨E⟩⟩ := Ambient.exists_ambient
  obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := E.solution_integral
  obtain ⟨red,rev⟩ := recorded_reductions
  have eu : E.eval recordedU = E.solution := by rw [← red,E.eval_reduced,E.eval_whole]
  have ev : E.eval recordedV = E.solution⁻¹ := by rw [← rev,E.eval_reverse,eu]
  refine ⟨u,v,E.inj ?_,E.inj ?_,E.inj ?_,E.inj ?_,Image.not_signed u (E.inj ?_)⟩
  · rw [map_mul,hu,← eu,E.cleared]
  · rw [map_mul,hv,← ev,E.cleared]
  · rw [map_mul,hu,hv,Units.mul_inv,map_one]
  · rw [map_mul,hu,hv,Units.inv_mul,map_one]
  · rw [map_mul,hu,← E.eval_whole,E.cleared]

theorem nontrivial_integral_unit :
    ∃ u : (MonoidAlgebra ℤ ElemP)ˣ,
      ∀ g : ElemP, (u : MonoidAlgebra ℤ ElemP) ≠ single g 1 ∧
                    (u : MonoidAlgebra ℤ ElemP) ≠ -single g 1 := by
  obtain ⟨u,v,_,uv,vu,support⟩ := integral_certificate
  exact ⟨⟨u,v,uv,vu⟩,support⟩

/-- The recorded construction also has nonmonomial coefficient reduction over F₂. -/
theorem nontrivial_reduction_certificate :
    ∃ u v : IntegralGroupRing, wordD whole*u=wordN whole ∧ u*v=1 ∧ v*u=1 ∧
      ∀ g : ElemP, modTwo u ≠ single g 1 := by
  obtain ⟨u,v,e,uv,vu,_⟩ := integral_certificate
  exact ⟨u,v,e,uv,vu,Binary.not_basis u e⟩

/-- A second integral witness belongs to the kernel of coefficient reduction modulo two. -/
theorem identity_reduction_certificate :
    ∃ h k : IntegralGroupRing, h*k=1 ∧ k*h=1 ∧ modTwo h=1 ∧
      ∀ g : ElemP, h ≠ single g 1 ∧ h ≠ -single g 1 := by
  obtain ⟨u,v,e,uv,vu,_⟩ := integral_certificate
  have im := congrArg Image.ρ e
  rw [map_mul,Image.evalD,Image.den_image,one_mul,Image.evalN,Image.full_num_image] at im
  refine ⟨u*twist v,twist u*v,?_,?_,?_,Image.sign_not_signed (Image.eval_sign_witness im uv)⟩
  · calc
      (u*twist v)*(twist u*v) = u*((twist v * twist u)*v) := by simp [mul_assoc]
      _ = 1 := by rw [← map_mul,vu,map_one,one_mul,uv]
  · calc
      (twist u*v)*(u*twist v) = twist u*((v*u)*twist v) := by simp [mul_assoc]
      _ = 1 := by rw [vu,one_mul,← map_mul,uv,map_one]
  · rw [map_mul, modTwo_twist, ← map_mul, uv, map_one]

/-- The same unit theorem for the abstract group on two generators and two relators. -/
theorem presented_nontrivial_integral_unit :
    ∃ u : (MonoidAlgebra ℤ Presentation.P)ˣ,
      ∀ g : Presentation.P, (u : MonoidAlgebra ℤ Presentation.P) ≠ single g 1 ∧
                            (u : MonoidAlgebra ℤ Presentation.P) ≠ -single g 1 := by
  obtain ⟨u,hu⟩ := nontrivial_integral_unit
  let f := mapDomainRingHom ℤ Presentation.equiv.symm
  have inj : Function.Injective f := mapDomain_injective Presentation.equiv.symm.injective
  refine ⟨Units.map f.toMonoidHom u, ?_⟩
  intro g
  obtain ⟨t,rfl⟩ := Presentation.equiv.symm.surjective g
  have bas : f (single t 1) = single (Presentation.equiv.symm t) 1 := mapDomain_single
  change f (u : IntegralGroupRing) ≠ _ ∧ f (u : IntegralGroupRing) ≠ _
  rw [← bas, ← map_neg]
  exact ⟨fun h => (hu t).1 (inj h),fun h => (hu t).2 (inj h)⟩

/-- One torsion-free group suffices to refute the universal assertion. -/
theorem integral_conjecture_false :
    ¬ (∀ (G : Type) [Group G],
      (∀ (g : G) (n : ℕ), 0<n → g^n=1 → g=1) →
      ∀ u : (MonoidAlgebra ℤ G)ˣ, ∃ g : G,
        (u : MonoidAlgebra ℤ G) = single g 1 ∨ (u : MonoidAlgebra ℤ G) = -single g 1) := by
  intro h
  obtain ⟨u,hu⟩ := nontrivial_integral_unit
  obtain ⟨g,e|e⟩ := h ElemP (fun _ _ hn hg => torsionFree hn hg) u
  · exact (hu g).1 e
  · exact (hu g).2 e

end
end Promislow

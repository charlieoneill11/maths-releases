import Promislow.Descent

namespace Promislow
variable {S : Type*} [Ring S] {O : Subring S} {f : S}

def conjugate (c x : Sˣ) := c*x*c⁻¹

theorem conjugate_inv (c x : Sˣ) : (conjugate c x)⁻¹=conjugate c x⁻¹ := by
  simp [conjugate,mul_assoc]
theorem conjugate_mul (c x y : Sˣ) : conjugate c (x*y)=conjugate c x*conjugate c y := by
  simp [conjugate,mul_assoc]

theorem near_mul {x y : S} {n : ℕ} (hyO : y∈O) (hx : Near O f n x) (hy : Near O f n y) :
    Near O f n (x*y) := by
  obtain ⟨s,hs,ex⟩ := hx
  obtain ⟨t,ht,ey⟩ := hy
  refine ⟨s*y+t,O.add_mem (O.mul_mem hs hyO) ht,?_⟩
  rw [ex,ey]; noncomm_ring

theorem nearUnit_mul {x y : Sˣ} {n : ℕ} (hf : f∈O) (hx : NearUnit O f n x)
    (hy : NearUnit O f n y) : NearUnit O f n (x*y) := by
  refine ⟨near_mul (value_mem' hf hy.1) hx.1 hy.1,?_⟩
  rw [mul_inv_rev]
  exact near_mul (value_mem' hf hx.2) hy.2 hx.2
where
  value_mem' {v : S} (h : f∈O) (p : Near O f n v) : v∈O := by
    obtain ⟨r,hr,rfl⟩ := p
    exact O.add_mem O.one_mem (O.mul_mem (O.pow_mem h _) hr)

theorem nearUnit_inv {x : Sˣ} {n : ℕ} (h : NearUnit O f n x) : NearUnit O f n x⁻¹ :=
  ⟨h.2,by simpa using h.1⟩

theorem near_inverse {x : Sˣ} {n : ℕ} (hx : Near O f n (x:S)) (hi : (↑x⁻¹:S) ∈ O) :
    Near O f n (↑x⁻¹:S) := by
  obtain ⟨t,ht,e⟩ := hx
  refine ⟨-(t*↑x⁻¹),O.neg_mem (O.mul_mem ht hi),?_⟩
  have hh : (1+f^n*t)*↑x⁻¹=1 := by rw [← e,Units.mul_inv]
  rw [add_mul,one_mul,mul_assoc] at hh
  rw [mul_neg,← hh]; abel

/-- The two directions of the midpoint calculation. -/
theorem half_conjugates (cf : ∀ z, Commute f z) {c : Sˣ} (hc : (c:S)∈O)
    (hi : f^4*(↑c⁻¹:S)∈O) {x p t r : S} (cp : Commute p (c:S))
    (xp : x=p+f^5*t) (ep : p=1+f*r) (ht : t∈O) (hr : r∈O) :
    Near O f 1 ((c:S)*x*↑c⁻¹) ∧ Near O f 1 ((↑c⁻¹:S)*x*c) := by
  have pL : (c:S)*p*↑c⁻¹=p := by rw [cp.symm.eq,mul_assoc,Units.mul_inv,mul_one]
  have pR : (↑c⁻¹:S)*p*c=p := by rw [mul_assoc,cp.eq,Units.inv_mul_cancel_left]
  have five : f^5=f*f^4 := pow_succ' _ _
  constructor
  · refine ⟨r + (c:S)*t*(f^4*↑c⁻¹),O.add_mem hr (O.mul_mem (O.mul_mem hc ht) hi),?_⟩
    rw [xp,mul_add,add_mul,pL,ep,pow_one,mul_add,add_assoc]
    simp only [mul_assoc]
    rw [((cf (c:S)).pow_left 5).symm.left_comm]
    simp only [five,mul_assoc,((cf (c:S)).pow_left 4).left_comm,((cf t).pow_left 4).left_comm]
  · refine ⟨r + (f^4*(↑c⁻¹:S))*t*c,O.add_mem hr (O.mul_mem (O.mul_mem hi ht) hc),?_⟩
    rw [xp,mul_add,add_mul,pR,ep,pow_one,mul_add,add_assoc]
    simp only [mul_assoc]
    rw [((cf (↑c⁻¹:S)).pow_left 5).symm.left_comm]
    simp only [five,mul_assoc]

theorem screw_comm {a b : Sˣ} {p t : S} (cf : ∀ z, Commute f z)
    (eb : (b:S)=p+f^5*t) (ca : Commute p (a:S))
    (ha : (a:S)∈O) (ht : t∈O) (hai : (↑a⁻¹:S)∈O) (hbi : (↑b⁻¹:S)∈O) :
    Near O f 5 (commWord a b : S) := by
  have e : (a:S)*b - (b:S)*a = f^5*((a:S)*t-t*a) := by
    rw [eb,mul_add,add_mul,ca.eq,((cf (a:S)).pow_left 5).symm.left_comm,mul_sub,mul_assoc]
    abel
  refine ⟨((a:S)*t-t*a)*↑a⁻¹*↑b⁻¹,O.mul_mem (O.mul_mem (O.sub_mem (O.mul_mem ha ht) (O.mul_mem ht ha)) hai) hbi,?_⟩
  change (a:S)*b*↑a⁻¹*↑b⁻¹=_
  rw [← mul_assoc,← mul_assoc,← e]
  simp [sub_mul,mul_assoc]

end Promislow

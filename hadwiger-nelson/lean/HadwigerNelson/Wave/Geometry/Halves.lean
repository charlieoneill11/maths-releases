import HadwigerNelson.Wave.Geometry

namespace HadwigerNelson.Wave
noncomputable section

def halfTile (W : Datum) (upper : Bool) : Set Plane :=
  tile W ∩ {p | if upper then H / 2 < p 1 else p 1 < H / 2}

def halfImage (reflected : Bool) (k : Fin 3) (z : Plane) : Plane :=
  tau (k.val : ℤ) (if reflected then sigma2 z else z)

/-- The twelve geometric representatives in Lemma 6. -/
def halfCopy (W : Datum) (reflected upper : Bool) (k : Fin 3) : Set Plane :=
  halfImage reflected k '' halfTile W upper

private theorem same_point {p q : Plane} (hx : p 0=q 0) (hy : p 1=q 1) : p=q := by
  ext i
  fin_cases i <;> assumption

theorem sigma1_involutive : Function.Involutive sigma1 := by
  intro z
  apply same_point <;> simp [sigma1]

theorem sigma2_involutive : Function.Involutive sigma2 := by
  intro z
  apply same_point <;> simp [sigma2]

theorem mem_tile_sigma1 (W : Datum) (z : Plane) : sigma1 z ∈ tile W ↔ z ∈ tile W := by
  change (0 < H-z 1 ∧ H-z 1 < H) ∧
      W.left (H-z 1) < z 0 ∧ z 0 < W.right (H-z 1) ↔ _
  rw [W.left_periodic.sub_eq',W.right_periodic.sub_eq',W.left_even,W.right_even]
  change _ ↔ (0 < z 1 ∧ z 1 < H) ∧ _
  constructor
  · rintro ⟨⟨ha,hb⟩,hl,hr⟩
    exact ⟨⟨by linarith,by linarith⟩,hl,hr⟩
  · rintro ⟨⟨ha,hb⟩,hl,hr⟩
    exact ⟨⟨by linarith,by linarith⟩,hl,hr⟩

theorem sigma1_low (W : Datum) : sigma1 '' halfTile W false = halfTile W true := by
  ext p
  constructor
  · rintro ⟨q,⟨ht,hh⟩,rfl⟩
    refine ⟨(mem_tile_sigma1 W q).2 ht,?_⟩
    change H / 2 < H-q 1
    change q 1 < H / 2 at hh
    linarith
  · rintro ⟨ht,hh⟩
    refine ⟨sigma1 p,⟨(mem_tile_sigma1 W p).2 ht,?_⟩,sigma1_involutive p⟩
    change H-p 1 < H/2
    change H/2 < p 1 at hh
    linarith

private def baseColumn (b : Bool) : ℤ := if b then -1 else 0
private def baseRow (b : Bool) (k : Fin 3) : ℤ := (k.val:ℤ) + if b then 2 else 0

private theorem rep_coords (W : Datum) (b : Bool) (k : Fin 3) (z : Plane) :
    point (localU W b (baseColumn b) (halfImage b k z))
          (localY b (baseColumn b) (halfImage b k z) - baseRow b k*H) = z := by
  apply same_point <;> cases b <;>
    simp [baseColumn,baseRow,localU,localY,halfImage,tau,sigma2] <;> ring

private theorem rep_copy (W : Datum) (b : Bool) (k : Fin 3) {z : Plane} (hz : z ∈ tile W) :
    InCopy W b (baseColumn b) (baseRow b k) (halfImage b k z) := by
  apply (inCopy_iff_tile ..).mpr
  rwa [rep_coords]

/-- Representatives cannot meet after any period shift unless all three
indices and the shift agree. This includes disjointness of translated copies
of a single representative. -/
theorem halfCopy_unique {W : Datum} {b b' h h' : Bool} {k k' : Fin 3} {v p : Plane}
    (hv : v ∈ lattice W) (hp : p ∈ halfCopy W b h k) (hp' : p+v ∈ halfCopy W b' h' k') :
    b=b' ∧ h=h' ∧ k=k' ∧ v=0 := by
  obtain ⟨i,j,rfl⟩ := (mem_lattice W _).mp hv
  obtain ⟨z,⟨hz,hzhalf⟩,rfl⟩ := hp
  obtain ⟨z',⟨hz',hzhalf'⟩,eq⟩ := hp'
  have c1 := (rep_copy W b k hz).add_latticePoint i j
  have c2 := rep_copy W b' k' hz'
  rw [eq] at c2
  obtain ⟨ei,rfl,ej⟩ := c1.unique c2
  have hi : i=0 := by omega
  subst i
  have hkk : k=k' := by
    apply Fin.ext
    have bound := k.isLt
    have bound' := k'.isLt
    unfold baseRow at ej
    omega
  subst k'
  have hj : j=0 := by omega
  subst j
  have v0 : latticePoint W 0 0 = 0 := by apply same_point <;> simp [latticePoint]
  rw [v0,add_zero] at eq
  have ezz : z'=z := by
    rw [← rep_coords W b k z',← rep_coords W b k z]
    congr 3
  subst z'
  refine ⟨rfl,?_,rfl,v0⟩
  cases h <;> cases h' <;> try rfl
  · change z 1 < H/2 at hzhalf
    change H/2 < z 1 at hzhalf'
    linarith
  · change H/2 < z 1 at hzhalf
    change z 1 < H/2 at hzhalf'
    linarith

theorem sigma1_isometry : Isometry sigma1 := by
  apply Isometry.of_dist_eq
  intro p q
  simp only [EuclideanSpace.dist_eq,Fin.sum_univ_two,sigma1,point_fst,point_snd,Real.dist_eq,sq_abs]
  congr 1 <;> ring

theorem sigma2_isometry : Isometry sigma2 := by
  apply Isometry.of_dist_eq
  intro p q
  simp only [EuclideanSpace.dist_eq,Fin.sum_univ_two,sigma2,point_fst,point_snd,Real.dist_eq,sq_abs]
  congr 1 <;> ring

theorem tau_isometry (k : ℤ) : Isometry (tau k) := by
  apply Isometry.of_dist_eq
  intro p q
  simp only [EuclideanSpace.dist_eq,Fin.sum_univ_two,tau,point_fst,point_snd,Real.dist_eq,sq_abs]
  congr 1 <;> ring

def sigma1Perm : Equiv.Perm Label := {
  toFun := sigma1Label, invFun := sigma1Label
  left_inv := by decide, right_inv := by decide }

def sigma2Perm : Equiv.Perm Label := {
  toFun := sigma2Label, invFun := sigma2Label
  left_inv := by decide, right_inv := by decide }

def tauPerm (k : ℤ) : Equiv.Perm Label := {
  toFun := tauLabel k, invFun := tauLabel (-k)
  left_inv := by rintro ⟨a,b⟩; simp [tauLabel]
  right_inv := by rintro ⟨a,b⟩; simp [tauLabel] }


end
end HadwigerNelson.Wave

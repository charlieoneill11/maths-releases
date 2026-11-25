import HadwigerNelson.Wave.Geometry
import Mathlib.Data.Real.Archimedean

namespace HadwigerNelson.Wave
open Set
noncomputable section

/-- The half-open rectangular fundamental cell at row period v. -/
def cell (W : Datum) (v : ℝ) : Set Plane := {z | z 0 ∈ Ico 0 (2*W.x) ∧ z 1 ∈ Ico 0 v}

private theorem int_rep (s y : ℝ) (hs : 0<s) : ∃! k : ℤ, y+s*k ∈ Ico 0 s := by
  let j := ⌊y/s⌋
  have lo := (le_div_iff₀ hs).mp (Int.floor_le (y/s))
  have hi := (div_lt_iff₀ hs).mp (Int.lt_floor_add_one (y/s))
  refine ⟨-j,?_,?_⟩
  · dsimp [j]
    push_cast
    constructor <;> linarith
  · intro k hk
    obtain ⟨a,b⟩ := hk
    have r : ⌊y/s⌋ = -k := by
      apply Int.floor_eq_iff.mpr
      constructor
      · apply (le_div_iff₀ hs).mpr
        push_cast
        linarith
      · apply (div_lt_iff₀ hs).mpr
        push_cast
        linarith
    dsimp [j]
    omega

private def gridPoint (W : Datum) (v : ℝ) (i j : ℤ) : Plane :=
  point (2*W.x*i) ((3/2)*H*i+v*j)

private theorem representative (W : Datum) (v : ℝ) (hv : 0<v) (G : AddSubgroup Plane)
    (coords : ∀ z, z∈G ↔ ∃ i j, z=gridPoint W v i j) :
    ∀ z : Plane, ∃! g : G, (g:Plane) + z ∈ cell W v := by
  intro z
  have hx : 0<2*W.x := by linarith [W.x_bounds.1]
  obtain ⟨i,hi,ui⟩ := int_rep (2*W.x) (z 0) hx
  obtain ⟨j,hj,uj⟩ := int_rep v (z 1+(3/2)*H*i) hv
  let w := gridPoint W v i j
  refine ⟨⟨w,(coords _).mpr ⟨i,j,rfl⟩⟩,?_,?_⟩
  · change (w 0+z 0 ∈ Ico 0 (2*W.x)) ∧ w 1 + z 1 ∈ Ico 0 v
    constructor
    · simpa [w,gridPoint,add_comm] using hi
    · simpa [w,gridPoint,add_assoc,add_left_comm,add_comm] using hj
  · rintro ⟨w',hw'⟩ good
    obtain ⟨i',j',rfl⟩ := (coords _).mp hw'
    obtain ⟨u',y'⟩ := good
    change 2*W.x*i'+z 0 ∈ Ico 0 (2*W.x) at u'
    change (3/2)*H*i'+v*j'+z 1 ∈ Ico 0 v at y'
    have ei := ui i' (by simpa [add_comm] using u')
    subst i'
    have ej := uj j' (by simpa [add_assoc,add_left_comm,add_comm] using y')
    subst j'
    rfl

theorem lattice_cell_rep (W : Datum) : ∀ z : Plane, ∃! g : lattice W, (g:Plane)+z∈cell W (3*H) :=
  representative W (3*H) (by linarith [H_pos]) _ (mem_lattice W)

theorem holeLattice_cell_rep (W : Datum) : ∀ z : Plane, ∃! g : holeLattice W, (g:Plane)+z∈cell W H :=
  representative W H H_pos _ (mem_holeLattice W)

end
end HadwigerNelson.Wave

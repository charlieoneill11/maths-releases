import HadwigerNelson.Plane
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace HadwigerNelson.Wave

noncomputable section

/-- The height of a tile. -/
def H : ℝ := 1 / 2

theorem H_pos : 0 < H := by norm_num [H]

def point (u y : ℝ) : Plane := !₂[u, y]

@[simp] theorem point_fst (u y : ℝ) : point u y 0 = u := rfl
@[simp] theorem point_snd (u y : ℝ) : point u y 1 = y := rfl

/-- A finite rational piecewise-affine presentation on the closed tile interval.
The quadruple lists the two endpoints, slope and intercept of a piece. -/
def RationalProfile (f : ℝ → ℝ) : Prop :=
  ∃ pieces : Finset (ℚ × ℚ × ℚ × ℚ), ∀ y ∈ Set.Icc 0 H, ∃ p ∈ pieces,
    y ∈ Set.Icc (p.1 : ℝ) (p.2.1 : ℝ) ∧
    ∀ z ∈ Set.Icc 0 H, z ∈ Set.Icc (p.1 : ℝ) (p.2.1 : ℝ) → f z = (p.2.2.1 : ℝ)*z + p.2.2.2

/-- Definition 4 uses the continuous periodic extensions of the two profile
functions. The reflection and complement identities are given on that extension. -/
structure Datum where
  x : ℝ
  x_rational : ∃ q : ℚ, x = q
  x_bounds : 9 / 10 < x ∧ x < 1
  left : ℝ → ℝ
  right : ℝ → ℝ
  left_rational : RationalProfile left
  right_rational : RationalProfile right
  left_continuous : Continuous left
  right_continuous : Continuous right
  left_periodic : Function.Periodic left H
  right_periodic : Function.Periodic right H
  left_even : ∀ y, left (-y) = left y
  right_even : ∀ y, right (-y) = right y
  complement : ∀ y, right y + right (y + H / 2) = 2*x
  left_antitone : AntitoneOn left (Set.Icc 0 (H / 2))
  y0 : ℝ
  y0_bounds : 0 ≤ y0 ∧ y0 < H / 4
  left_zero : ∀ y ∈ Set.Icc y0 (H / 2), left y = 0
  left_bounds : ∀ y, 0 ≤ left y ∧ left y < 1 / 5
  right_bounds : ∀ y, 4 / 5 < right y ∧ right y < 1

abbrev Label := Bool × ZMod 3

@[local simp] private theorem three_mod : (3 : ZMod 3) = 0 := by decide

def tile (W : Datum) : Set Plane := {z | z 1 ∈ Set.Ioo 0 H ∧ z 0 ∈ Set.Ioo (W.left (z 1)) (W.right (z 1))}

def hole (W : Datum) : Set Plane := {z | |z 1| ≤ W.y0 ∧ |z 0| ≤ W.left (z 1)}

def sigma1 (z : Plane) : Plane := point (z 0) (H - z 1)
def sigma2 (z : Plane) : Plane := point (-z 0) (z 1)
def tau (j : ℤ) (z : Plane) : Plane := point (z 0) (z 1 + j*H)

def latticePoint (W : Datum) (i j : ℤ) : Plane :=
  point (2*W.x*i) ((3/2)*H*i + 3*H*j)

def holeLatticePoint (W : Datum) (i j : ℤ) : Plane :=
  point (2*W.x*i) ((3/2)*H*i + H*j)

private theorem point_ext {a b : Plane} (hu : a 0 = b 0) (hy : a 1 = b 1) : a = b := by
  ext i
  fin_cases i <;> assumption

private def periodGroup (W : Datum) (v : ℝ) : AddSubgroup Plane where
  carrier := {z | ∃ i j : ℤ, z = point (2*W.x*i) ((3/2)*H*i + v*j)}
  zero_mem' := ⟨0,0, by apply point_ext <;> simp⟩
  add_mem' := by
    rintro _ _ ⟨i,j,rfl⟩ ⟨k,l,rfl⟩
    refine ⟨i+k,j+l,?_⟩
    apply point_ext <;> simp <;> ring
  neg_mem' := by
    rintro _ ⟨i,j,rfl⟩
    refine ⟨-i,-j,?_⟩
    apply point_ext <;> simp <;> ring

def lattice (W : Datum) : AddSubgroup Plane := periodGroup W (3*H)
def holeLattice (W : Datum) : AddSubgroup Plane := periodGroup W H

theorem mem_lattice (W : Datum) (z : Plane) : z ∈ lattice W ↔ ∃ i j, z = latticePoint W i j := Iff.rfl
theorem mem_holeLattice (W : Datum) (z : Plane) : z ∈ holeLattice W ↔ ∃ i j, z = holeLatticePoint W i j := Iff.rfl

private instance periodGroup_countable (W : Datum) (v : ℝ) : Countable (periodGroup W v) := by
  let f : ℤ × ℤ → periodGroup W v := fun ij =>
    ⟨point (2*W.x*ij.1) ((3/2)*H*ij.1 +v*ij.2),ij.1,ij.2,rfl⟩
  apply Function.Surjective.countable (f := f)
  rintro ⟨z,i,j,rfl⟩
  exact ⟨(i,j),rfl⟩

instance (W : Datum) : Countable (lattice W) := periodGroup_countable W _
instance (W : Datum) : Countable (holeLattice W) := periodGroup_countable W _

theorem vertical_unit_mem (W : Datum) : point 0 1 ∈ holeLattice W := by
  refine (mem_holeLattice W _).2 ⟨0,2,?_⟩
  apply point_ext <;> norm_num [holeLatticePoint,H]

/-- The horizontal coordinate points inward from the relevant column wall. -/
def localU (W : Datum) (side : Bool) (i : ℤ) (z : Plane) : ℝ :=
  if side then 2*W.x*((i:ℝ)+1) - z 0 else z 0 - 2*W.x*i

/-- The vertical coordinate includes the half-height shift of the mirror tile. -/
def localY (side : Bool) (i : ℤ) (z : Plane) : ℝ :=
  z 1 - (3/2)*H*i + if side then H/2 else 0

/-- Membership in the open tile copy in column i and lifted row j. -/
def InCopy (W : Datum) (side : Bool) (i j : ℤ) (z : Plane) : Prop :=
  (j:ℝ)*H < localY side i z ∧ localY side i z < ((j:ℝ)+1)*H ∧
  W.left (localY side i z) < localU W side i z ∧ localU W side i z < W.right (localY side i z)

def HasLabel (W : Datum) (z : Plane) (c : Label) : Prop :=
  ∃ i j : ℤ, (j : ZMod 3) = c.2 ∧ InCopy W c.1 i j z

/-- Return the unique labelled tile containing the point, with none denoting blank. -/
def colour (W : Datum) (z : Plane) : Option Label := by
  classical
  exact if h : ∃ c, HasLabel W z c then some h.choose else none

theorem tile_open (W : Datum) : IsOpen (tile W) := by
  have hu : Continuous (fun z : Plane => z 0) := PiLp.continuous_apply ..
  have hy : Continuous (fun z : Plane => z 1) := PiLp.continuous_apply ..
  exact ((isOpen_lt continuous_const hy).inter (isOpen_lt hy continuous_const)).inter
    ((isOpen_lt (W.left_continuous.comp hy) hu).inter (isOpen_lt hu (W.right_continuous.comp hy)))

private theorem interior_index_unique {s a : ℝ} {i k : ℤ} (hs : 0 < s)
    (h₁ : s*i < a) (h₂ : a < s*((i:ℝ)+1)) (h₃ : s*k < a) (h₄ : a < s*((k:ℝ)+1)) : i = k := by
  rcases lt_trichotomy i k with h | h | h
  · have hi : (i:ℝ)+1 ≤ k := by exact_mod_cast (show i+1 ≤ k by omega)
    linarith [mul_le_mul_of_nonneg_left hi hs.le]
  · exact h
  · have hk : (k:ℝ)+1 ≤ i := by exact_mod_cast (show k+1 ≤ i by omega)
    linarith [mul_le_mul_of_nonneg_left hk hs.le]

theorem InCopy.column_bounds {W : Datum} {b i j z} (h : InCopy W b i j z) :
    2*W.x*i < z 0 ∧ z 0 < 2*W.x*((i:ℝ)+1) := by
  obtain ⟨_,_,hl,hr⟩ := h
  have h₁ := (W.left_bounds (localY b i z)).1
  have h₂ := (W.right_bounds (localY b i z)).2
  have hx := W.x_bounds.1
  cases b <;> simp only [localU, Bool.false_eq_true, if_false, if_true] at hl hr <;> constructor <;> linarith

theorem InCopy.unique {W : Datum} {b b' i i' j j' z} (h : InCopy W b i j z)
    (h' : InCopy W b' i' j' z) : i=i' ∧ b=b' ∧ j=j' := by
  have hc : i=i' := interior_index_unique (by linarith [W.x_bounds.1]) h.column_bounds.1
    h.column_bounds.2 h'.column_bounds.1 h'.column_bounds.2
  subst i'
  have hs : b=b' := by
    by_contra hn
    have w := W.complement (z 1 - (3/2)*H*i)
    have h₁ := h.2.2.2
    have h₂ := h'.2.2.2
    cases b <;> cases b' <;> simp_all [localU,localY] <;> linarith
  subst b'
  refine ⟨rfl,rfl,?_⟩
  apply interior_index_unique H_pos
  · simpa [mul_comm] using h.1
  · simpa [mul_comm] using h.2.1
  · simpa [mul_comm] using h'.1
  · simpa [mul_comm] using h'.2.1

theorem HasLabel.unique {W : Datum} {z c d} (h : HasLabel W z c) (h' : HasLabel W z d) : c=d := by
  obtain ⟨i,j,hj,hw⟩ := h
  obtain ⟨i',j',hj',hw'⟩ := h'
  obtain ⟨_,hs,rfl⟩ := hw.unique hw'
  exact Prod.ext hs (hj.symm.trans hj')

theorem colourClass_iff (W : Datum) (z : Plane) (c : Label) :
    colour W z = some c ↔ HasLabel W z c := by
  classical
  unfold colour
  split <;> rename_i h
  · exact ⟨fun e => Option.some.inj e ▸ h.choose_spec, fun hc => congrArg some (h.choose_spec.unique hc)⟩
  · constructor
    · intro e
      cases e
    · intro hc
      exact (h ⟨c,hc⟩).elim

/-- Coordinates relative to the given row yield precisely the open tile T. -/
theorem inCopy_iff_tile (W : Datum) (b : Bool) (i j : ℤ) (z : Plane) :
    InCopy W b i j z ↔ point (localU W b i z) (localY b i z - j*H) ∈ tile W := by
  change _ ↔ (0 < localY b i z - j*H ∧ localY b i z - j*H < H) ∧
    W.left (localY b i z - j*H) < _ ∧ _ < W.right (localY b i z - j*H)
  rw [W.left_periodic.sub_int_mul_eq j, W.right_periodic.sub_int_mul_eq j]
  unfold InCopy
  constructor
  · rintro ⟨ha,hb,hl,hr⟩
    exact ⟨⟨by linarith,by linarith⟩,hl,hr⟩
  · rintro ⟨⟨ha,hb⟩,hl,hr⟩
    exact ⟨by linarith,by linarith,hl,hr⟩

private theorem InCopy.move {W : Datum} {b i j z} (h : InCopy W b i j z)
    {b' i' z'} (k : ℤ)
    (hu : localU W b' i' z' = localU W b i z)
    (hy : localY b' i' z' = localY b i z + k*H) : InCopy W b' i' (j+k) z' := by
  unfold InCopy at *
  rw [hu,hy,W.left_periodic.int_mul k,W.right_periodic.int_mul k,Int.cast_add]
  exact ⟨by linarith [h.1],by linarith [h.2.1],h.2.2⟩

private theorem InCopy.flip {W : Datum} {b i j z} (h : InCopy W b i j z)
    {z'} (k : ℤ) (hu : localU W b i z' = localU W b i z)
    (hy : localY b i z' = k*H - localY b i z) : InCopy W b i (k-j-1) z' := by
  unfold InCopy at *
  rw [hu,hy,W.left_periodic.int_mul_sub_eq k,W.right_periodic.int_mul_sub_eq k,
    W.left_even,W.right_even]
  push_cast
  exact ⟨by linarith [h.2.1],by linarith [h.1],h.2.2⟩

theorem InCopy.add_latticePoint {W : Datum} {b i j z} (h : InCopy W b i j z) (a k : ℤ) :
    InCopy W b (i+a) (j+3*k) (z + latticePoint W a k) := by
  apply h.move (3*k)
  · cases b <;> simp [localU,latticePoint] <;> ring
  · cases b <;> simp [localY,latticePoint] <;> ring

theorem colour_periodic (W : Datum) (z v : Plane) (hv : v ∈ lattice W) :
    colour W (z+v) = colour W z := by
  have move {z' v' : Plane} {c : Label} (hv' : v' ∈ lattice W) (h : HasLabel W z' c) :
      HasLabel W (z'+v') c := by
    obtain ⟨a,k,rfl⟩ := (mem_lattice W v').mp hv'
    obtain ⟨i,j,hj,h⟩ := h
    refine ⟨i+a,j+3*k,?_,h.add_latticePoint a k⟩
    push_cast
    simpa using hj
  apply Option.ext
  intro c
  rw [colourClass_iff,colourClass_iff]
  exact ⟨fun h => by simpa using move ((lattice W).neg_mem hv) h, move hv⟩

/-- Horizontal reflection interchanges first- and second-orientation rows. -/
theorem InCopy.sigma2 {W : Datum} {b i j z} (h : InCopy W b i j z) :
    InCopy W (!b) (-i-1) (j+(3*i+if b then 1 else 2)) (sigma2 z) := by
  apply h.move
  · cases b <;> simp [localU,Wave.sigma2] <;> ring
  · cases b <;> simp [localY,Wave.sigma2] <;> ring

theorem InCopy.sigma1 {W : Datum} {b i j z} (h : InCopy W b i j z) :
    InCopy W b i ((1+(if b then 1 else 0)-3*i)-j-1) (sigma1 z) := by
  apply h.flip
  · cases b <;> simp [localU,Wave.sigma1]
  · cases b <;> simp [localY,Wave.sigma1] <;> ring

theorem InCopy.tau {W : Datum} {b i j z} (h : InCopy W b i j z) (k : ℤ) :
    InCopy W b i (j+k) (tau k z) := by
  apply h.move
  · cases b <;> simp [localU,Wave.tau]
  · cases b <;> simp [localY,Wave.tau] <;> ring

def sigma1Label (c : Label) : Label := (c.1, (if c.1 then 1 else 0)-c.2)
def sigma2Label (c : Label) : Label := (!c.1, c.2 + (if c.1 then 1 else 2))
def tauLabel (k : ℤ) (c : Label) : Label := (c.1, c.2+k)

theorem HasLabel.sigma1 {W : Datum} {z c} (h : HasLabel W z c) :
    HasLabel W (sigma1 z) (sigma1Label c) := by
  obtain ⟨i,j,hj,hw⟩ := h
  refine ⟨_,_,?_,hw.sigma1⟩
  cases c with | mk b k =>
    cases b <;> simp_all [sigma1Label] <;> ring

theorem HasLabel.sigma2 {W : Datum} {z c} (h : HasLabel W z c) :
    HasLabel W (sigma2 z) (sigma2Label c) := by
  obtain ⟨i,j,hj,hw⟩ := h
  refine ⟨_,_,?_,hw.sigma2⟩
  cases c with | mk b k =>
    cases b <;> simp_all [sigma2Label] <;> ring

theorem HasLabel.tau {W : Datum} {z c} (h : HasLabel W z c) (k : ℤ) :
    HasLabel W (tau k z) (tauLabel k c) := by
  obtain ⟨i,j,hj,hw⟩ := h
  refine ⟨_,_,?_,hw.tau k⟩
  simp [tauLabel,Int.cast_add,hj]

private theorem colour_move {W : Datum} (f g : Plane → Plane) (sig rev : Label → Label)
    (forward : ∀ {z c}, HasLabel W z c → HasLabel W (f z) (sig c))
    (backward : ∀ {z c}, HasLabel W z c → HasLabel W (g z) (rev c))
    (inv : Function.LeftInverse g f) (z : Plane) : colour W (f z) = (colour W z).map sig := by
  cases hz : colour W z with
  | some c =>
    exact (colourClass_iff ..).2 (forward ((colourClass_iff ..).1 hz))
  | none =>
    cases hf : colour W (f z) with
    | none => rfl
    | some c =>
      have h := backward ((colourClass_iff ..).1 hf)
      rw [inv] at h
      have he := (colourClass_iff ..).2 h
      simp [hz] at he

theorem colour_sigma1 (W : Datum) (z : Plane) :
    colour W (sigma1 z) = (colour W z).map sigma1Label := by
  apply colour_move sigma1 sigma1 sigma1Label sigma1Label HasLabel.sigma1 HasLabel.sigma1 _ z
  intro p
  apply point_ext <;> simp [sigma1]

theorem colour_sigma2 (W : Datum) (z : Plane) :
    colour W (sigma2 z) = (colour W z).map sigma2Label := by
  apply colour_move sigma2 sigma2 sigma2Label sigma2Label HasLabel.sigma2 HasLabel.sigma2 _ z
  intro p
  apply point_ext <;> simp [sigma2]

theorem colour_tau (W : Datum) (k : ℤ) (z : Plane) :
    colour W (tau k z) = (colour W z).map (tauLabel k) := by
  apply colour_move (tau k) (tau (-k)) (tauLabel k) (tauLabel (-k))
    (fun h => h.tau k) (fun h => h.tau (-k)) _ z
  intro p
  apply point_ext <;> simp [tau] <;> ring

theorem localU_continuous (W : Datum) (b : Bool) (i : ℤ) : Continuous (localU W b i) := by
  have u : Continuous (fun p : Plane => p 0) := PiLp.continuous_apply ..
  cases b
  · exact u.sub continuous_const
  · exact continuous_const.sub u

theorem localY_continuous (b : Bool) (i : ℤ) : Continuous (localY b i) :=
  ((PiLp.continuous_apply ..).sub continuous_const).add continuous_const

theorem inCopy_open (W : Datum) (b : Bool) (i j : ℤ) : IsOpen {z | InCopy W b i j z} := by
  let u := localU_continuous W b i
  let y := localY_continuous b i
  exact (isOpen_lt continuous_const y).inter ((isOpen_lt y continuous_const).inter
    ((isOpen_lt (W.left_continuous.comp y) u).inter (isOpen_lt u (W.right_continuous.comp y))))

theorem colour_fibre_open (W : Datum) (c : Label) : IsOpen {z | colour W z = some c} := by
  have eq : {z | colour W z = some c} =
      ⋃ i : ℤ, ⋃ j : {j : ℤ // (j : ZMod 3) = c.2}, {z | InCopy W c.1 i j.val z} := by
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_iUnion,colourClass_iff,HasLabel]
    constructor
    · rintro ⟨i,j,hj,h⟩
      exact ⟨i,⟨j,hj⟩,h⟩
    · rintro ⟨i,⟨j,hj⟩,h⟩
      exact ⟨i,j,hj,h⟩
  rw [eq]
  exact isOpen_iUnion fun i => isOpen_iUnion fun j => inCopy_open W c.1 i j.val

theorem blank_closed (W : Datum) : IsClosed {z | colour W z = none} := by
  have eq : {z | colour W z = none} = (⋃ c : Label, {z | colour W z = some c})ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_compl_iff,Set.mem_iUnion]
    cases colour W z <;> simp
  rw [eq]
  exact (isOpen_iUnion (colour_fibre_open W)).isClosed_compl

end

end HadwigerNelson.Wave

import HadwigerNelson.Wave.Geometry
import Mathlib.Data.Real.Archimedean

namespace HadwigerNelson.Wave
noncomputable section

/-- Supporting column boundaries, horizontal row lines, and interfaces between the two tile orientations. -/
def seams (W : Datum) : Set Plane := {z |
  (∃ i : ℤ, z 0 = 2*W.x*i) ∨
  (∃ i j : ℤ, z 1 - (3/2)*H*i = (j:ℝ)*H/2) ∨
  (∃ i : ℤ, z 0 - 2*W.x*i = W.right (z 1 - (3/2)*H*i))}

def holeCopies (W : Datum) : Set Plane := {z | ∃ i j : ℤ, z - holeLatticePoint W i j ∈ hole W}

private theorem floor_interval (v s : ℝ) (hs : 0<s) :
    ∃ j : ℤ, (j:ℝ)*s  ≤  v ∧ v < ((j:ℝ)+1)*s := by
  refine ⟨⌊v/s⌋,?_,?_⟩
  · exact (le_div_iff₀ hs).mp (Int.floor_le _)
  · exact (div_lt_iff₀ hs).mp (Int.lt_floor_add_one _)

private theorem Datum.left_abs (W : Datum) (y : ℝ) : W.left |y| = W.left y := by
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]
  · rw [abs_of_neg hy,W.left_even]

private theorem near_wall {W : Datum} {z : Plane} (i : ℤ) (hn : z 0 ≠ 2*W.x*i)
    (hu : |z 0 - 2*W.x*i|  ≤  W.left (z 1-(3/2)*H*i)) : z ∈ holeCopies W := by
  let t := z 1 - (3/2)*H*i
  obtain ⟨j,hlo,hhi⟩ := floor_interval (t+H/2) H H_pos
  let dy := t - j*H
  have hdy : |dy|  ≤  H/2 := by
    rw [abs_le]; dsimp [dy]; constructor <;> linarith
  have per : W.left dy = W.left t := W.left_periodic.sub_int_mul_eq j
  have hp : 0 < W.left dy := by rw [per]; exact lt_of_lt_of_le (abs_pos.mpr (sub_ne_zero.mpr hn)) hu
  have hcut : |dy|  ≤  W.y0 := by
    by_contra! bad
    have hz := W.left_zero |dy| ⟨bad.le,hdy⟩
    rw [W.left_abs] at hz
    linarith
  refine ⟨i,j,?_⟩
  change |z 1 - ((3/2)*H*i+H*j)|  ≤  W.y0 ∧
    |z 0 - 2*W.x*i|  ≤  W.left (z 1 - ((3/2)*H*i+H*j))
  have eq : z 1 - ((3/2)*H*i+H*j) = dy := by dsimp [dy,t]; ring
  rw [eq,per]
  exact ⟨hcut,hu⟩

private theorem label_of_strict {W : Datum} {b i z} (hl : W.left (localY b i z) < localU W b i z)
    (hr : localU W b i z < W.right (localY b i z)) (hs : z ∉ seams W) :
    ∃ c, colour W z = some c := by
  obtain ⟨j,lo,hi⟩ := floor_interval (localY b i z) H H_pos
  have lt' : (j:ℝ)*H < localY b i z := by
    refine lo.lt_of_ne ?_
    intro eq
    apply hs
    right; left
    refine ⟨i,2*j-(if b then 1 else 0),?_⟩
    cases b <;> simp [localY] at eq ⊢ <;> linarith
  exact ⟨(b,(j:ZMod 3)),(colourClass_iff ..).mpr ⟨i,j,rfl,lt',hi,hl,hr⟩⟩

/-- Away from both horizontal row boundaries and from the interface, every
point inside the fundamental column of a complete wave has a label. -/
theorem not_blank_inside_first_column (W : Datum) (hl : W.left = fun _ => 0) {u y : ℝ}
    (hu : 0 < u ∧ u < 2*W.x) (hy0 : ∀ j : ℤ, y ≠ j*H)
    (hyhalf : ∀ j : ℤ, y+H/2 ≠ j*H) (hseam : u ≠ W.right y) :
    colour W (point u y) ≠ none := by
  have labelled (b : Bool) (lu : 0 < localU W b 0 (point u y))
      (ru : localU W b 0 (point u y) < W.right (localY b 0 (point u y)))
      (notrow : ∀ j : ℤ, localY b 0 (point u y) ≠ j*H) :
      colour W (point u y) ≠ none := by
    obtain ⟨j,lo,hi⟩ := floor_interval (localY b 0 (point u y)) H H_pos
    have ins : InCopy W b 0 j (point u y) := ⟨lo.lt_of_ne (notrow j).symm,hi,by rwa [hl],ru⟩
    have e := (colourClass_iff W (point u y) (b,(j:ZMod 3))).mpr ⟨0,j,rfl,ins⟩
    rw [e]
    simp
  rcases lt_or_gt_of_ne hseam with left | right
  · apply labelled false
    · simpa [localU] using hu.1
    · simpa [localU,localY] using left
    · simpa [localY] using hy0
  · apply labelled true
    · simpa [localU] using sub_pos.mpr hu.2
    · simp only [localU,localY,if_true,point_fst,point_snd,Int.cast_zero,mul_zero,sub_zero,zero_add,mul_one]
      linarith [W.complement y]
    · simpa [localY] using hyhalf

theorem blank_subset_holes_seams (W : Datum) : {z | colour W z = none} ⊆ holeCopies W ∪ seams W := by
  intro z hz
  by_cases seam : z ∈ seams W
  · exact Or.inr seam
  left
  have hx : 0 < 2*W.x := by linarith [W.x_bounds.1]
  obtain ⟨i,hi,hi'⟩ := floor_interval (z 0) (2*W.x) hx
  let t := z 1 - (3/2)*H*i
  let u := z 0 - 2*W.x*i
  have noWall (k : ℤ) : z 0 ≠ 2*W.x*k := fun h => seam (Or.inl ⟨k,h⟩)
  have noMid : u ≠ W.right t := fun h => seam (Or.inr (Or.inr ⟨i,h⟩))
  have blank : ¬∃ c, colour W z = some c := by
    change colour W z = none at hz
    simp [hz]
  have u0 : 0  ≤  u := by dsimp [u]; linarith
  rcases lt_or_gt_of_ne noMid with h | h
  · by_cases wall : u  ≤  W.left t
    · exact near_wall i (noWall i) (by rw [abs_of_nonneg u0]; exact wall)
    · exact (blank (label_of_strict (b:=false) (i:=i)
        (by simpa [localU,localY,t,u] using lt_of_not_ge wall) (by simpa [localU,localY,t,u] using h) seam)).elim
  · let t' := t + H/2
    let u' := 2*W.x*((i:ℝ)+1) - z 0
    have per : W.left (z 1-(3/2)*H*(i+1)) = W.left t' := by
      rw [show z 1-(3/2)*H*(i+1) = t'-(2:ℤ)*H by dsimp [t',t]; push_cast; ring,
        W.left_periodic.sub_int_mul_eq]
    by_cases wall : u'  ≤  W.left t'
    · apply near_wall (i+1) (noWall _)
      push_cast
      rw [per,abs_of_nonpos (by linarith)]
      dsimp [u'] at wall
      linarith
    · apply (blank _).elim
      apply label_of_strict (b:=true) (i:=i) (z:=z) _ _ seam
      · simpa [localU,localY,u',t',t] using lt_of_not_ge wall
      · change u' < W.right t'
        dsimp [u'] ; dsimp [u] at h
        have eq : W.right t + W.right t' = 2*W.x := W.complement t
        linarith

private theorem InCopy.away_from_wall {W : Datum} {b i j z} (h : InCopy W b i j z) (k : ℤ) :
    W.left (z 1-(3/2)*H*k) < |z 0-2*W.x*k| := by
  obtain ⟨lo,hi⟩ := h.column_bounds
  have hx := W.x_bounds.1
  have hl := (W.left_bounds (z 1-(3/2)*H*k)).2
  have hd := h.2.2.1
  have he := h.2.2.2
  have hr := (W.right_bounds (localY b i z)).2
  rcases lt_trichotomy k i with hki | hki | hik
  · have kle : (k:ℝ)+1  ≤  i := by exact_mod_cast (show k+1  ≤  i by omega)
    have sk := mul_le_mul_of_nonneg_left kle (show 0 ≤ 2*W.x by linarith)
    linarith [le_abs_self (z 0-2*W.x*k)]
  · subst k
    cases b
    · exact lt_of_lt_of_le (by simpa [localU,localY] using hd) (le_abs_self _)
    · simp [localU,localY] at he hr
      linarith [le_abs_self (z 0-2*W.x*i)]
  · by_cases next : k=i+1
    · subst k
      push_cast at *
      cases b
      · simp [localU,localY] at he hr
        linarith [neg_le_abs (z 0-2*W.x*((i:ℝ)+1))]
      · let t := localY true i z
        have eq : z 1-(3/2)*H*((i:ℝ)+1) = t-(2:ℤ)*H := by
          simp [t,localY]; ring
        rw [eq,W.left_periodic.sub_int_mul_eq]
        apply lt_of_lt_of_le hd
        change 2*W.x*((i:ℝ)+1) - z 0  ≤  |z 0-2*W.x*((i:ℝ)+1)|
        linarith [neg_le_abs (z 0-2*W.x*((i:ℝ)+1))]
    · have kle : (i:ℝ)+2  ≤  k := by exact_mod_cast (show i+2 ≤ k by omega)
      have sk := mul_le_mul_of_nonneg_left kle (show 0 ≤ 2*W.x by linarith)
      linarith [neg_le_abs (z 0-2*W.x*k)]

theorem holeCopies_subset_blank (W : Datum) : holeCopies W ⊆ {z | colour W z = none} := by
  rintro z ⟨k,l,holemem⟩
  change colour W z = none
  cases h : colour W z with
  | none => rfl
  | some c =>
    obtain ⟨i,j,_,hc⟩ := (colourClass_iff ..).mp h
    have outside := hc.away_from_wall k
    have inside := holemem.2
    change |z 0-2*W.x*k|  ≤  W.left (z 1-((3/2)*H*k + H*l)) at inside
    rw [show z 1-((3/2)*H*k+H*l) = (z 1-(3/2)*H*k) - l*H by ring,
      W.left_periodic.sub_int_mul_eq] at inside
    exact (not_lt_of_ge inside outside).elim

theorem holeCopies_disjoint {W : Datum} {z : Plane} {i j i' j' : ℤ}
    (h : z-holeLatticePoint W i j ∈ hole W) (h' : z-holeLatticePoint W i' j' ∈ hole W) :
    i=i' ∧ j=j' := by
  obtain ⟨a,b⟩ := h; obtain ⟨a',b'⟩ := h'
  simp only [PiLp.sub_apply,holeLatticePoint,point_fst,point_snd] at a b a' b'
  have u := lt_of_le_of_lt b (W.left_bounds _).2
  have u' := lt_of_le_of_lt b' (W.left_bounds _).2
  rw [abs_lt] at u u'
  rw [abs_le] at a a'
  have hx := W.x_bounds.1
  have hi : i=i' := by
    rcases lt_trichotomy i i' with h | h | h
    · have e : (i:ℝ)+1  ≤  i' := by exact_mod_cast (show i+1 ≤ i' by omega)
      linarith [mul_le_mul_of_nonneg_left e (show 0 ≤ 2*W.x by linarith),u.1,u'.2,u.2,u'.1]
    · exact h
    · have e : (i':ℝ)+1  ≤  i := by exact_mod_cast (show i'+1 ≤ i by omega)
      linarith [mul_le_mul_of_nonneg_left e (show 0 ≤ 2*W.x by linarith),u.1,u'.2,u.2,u'.1]
  subst i'
  refine ⟨rfl,?_⟩
  have bounds := W.y0_bounds.2
  rcases lt_trichotomy j j' with h | h | h
  · have e : (j:ℝ)+1  ≤  j' := by exact_mod_cast (show j+1 ≤ j' by omega)
    linarith [mul_le_mul_of_nonneg_left e H_pos.le,a.1,a'.2,a.2,a'.1,H_pos]
  · exact h
  · have e : (j':ℝ)+1  ≤  j := by exact_mod_cast (show j'+1 ≤ j by omega)
    linarith [mul_le_mul_of_nonneg_left e H_pos.le,a.1,a'.2,a.2,a'.1,H_pos]

end
end HadwigerNelson.Wave

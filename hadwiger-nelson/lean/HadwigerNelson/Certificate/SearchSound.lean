import HadwigerNelson.Certificate.BoxSearch
import HadwigerNelson.Certificate.Enclosure

namespace HadwigerNelson.Certificate.ParameterBoxes

def Range.Contains (r : Range) (x : ℕ) : Prop := r.lo ≤ x ∧ x ≤ r.hi
def Box.Contains (b : Box) (m s j : ℕ) : Prop := b.m.Contains m ∧ b.s.Contains s ∧ b.j.Contains j

private noncomputable def Range.enclose (r : Range) (x : ℕ) (h : r.Contains x) : Enclosed :=
  ⟨r.interval, x, by
    have hl := h.1
    have hr := h.2
    unfold Range.interval Interval.Contains
    push_cast
    exact ⟨by exact_mod_cast hl, by exact_mod_cast hr⟩⟩

private theorem clip_contains {b : Box} {m s j : ℕ} (z : b.Contains m s j) (hsj : s+j ≤ 10689) :
    b.clip.Contains m s j := by
  rcases z with ⟨hm,⟨sl,sh⟩,jl,jh⟩
  exact ⟨hm,⟨sl,le_min sh (by omega)⟩,⟨jl,le_min jh (by omega)⟩⟩

private theorem cut_cover {r : Range} {x : ℕ} (hx : r.Contains x) :
    r.cut.1.Contains x ∨ r.cut.2.Contains x := by
  by_cases h : x ≤ (r.lo+r.hi)/2
  · exact Or.inl ⟨hx.1,h⟩
  · exact Or.inr ⟨by change (r.lo+r.hi)/2+1 ≤ x; omega,hx.2⟩

private theorem split_cover {b : Box} {m s j : ℕ} (h : b.Contains m s j) :
    b.split.1.Contains m s j ∨ b.split.2.Contains m s j := by
  rcases h with ⟨hm,hs,hj⟩
  unfold Box.split
  dsimp only
  split
  · exact (cut_cover hm).imp (fun l => ⟨l,hs,hj⟩) (fun r => ⟨r,hs,hj⟩)
  · split
    · exact (cut_cover hs).imp (fun l => ⟨hm,l,hj⟩) (fun r => ⟨hm,r,hj⟩)
    · exact (cut_cover hj).imp (fun l => ⟨hm,hs,l⟩) (fun r => ⟨hm,hs,r⟩)

/-- The early exit uses the nonnegativity of the physical centre credit.
The full evaluation bounds each of its two profile credits from below. -/
theorem upper_sound (b : Box) (m s j : ℕ) (inside : b.Contains m s j) (feasible : s+j ≤ 10689) :
    objective (m:ℝ) s j (s+j:ℕ) ≤ (b.upper:ℝ) := by
  rcases inside with ⟨hm,hs,hj⟩
  let M := b.m.enclose m hm
  let S := b.s.enclose s hs
  let J := b.j.enclose j hj
  let H : Enclosed := ⟨b.omitted,(s+j:ℕ),by
    unfold Box.omitted Interval.Contains
    push_cast
    constructor
    · exact_mod_cast Nat.add_le_add hs.1 hj.1
    · exact_mod_cast le_min feasible (Nat.add_le_add hs.2 hj.2)⟩
  let B := budgets M.value S.value J.value H.value (variance M.value)
  have upper := (firstTerms_sound M S J).2
  have nonneg := (credit_nonneg B (230/10^10) (79/10^10) (980/10^10)).trans
    (le_max_left _ (credit B (259/10^10) (93/10^10) (1100/10^10)))
  unfold Box.upper
  dsimp only
  split
  · exact (sub_le_self _ nonneg).trans upper
  · have r := (credit_sound M S J H (230/10^10) (79/10^10) (980/10^10)).1
    have d := (credit_sound M S J H (259/10^10) (93/10^10) (1100/10^10)).1
    rw [Rat.cast_sub,Rat.cast_max]
    exact sub_le_sub upper (max_le_max r d)

theorem checkBox_sound (fuel : ℕ) (b : Box) (m s j : ℕ) (h : b.Contains m s j)
    (hsj : s+j ≤ 10689) (pass : checkBox fuel b = true) :
    objective (m:ℝ) s j (s+j:ℕ) < 1 := by
  induction fuel generalizing b with
  | zero => simp [checkBox] at pass
  | succ n ih =>
    have sl := h.2.1.1
    have jl := h.2.2.1
    have possible : ¬10689 < b.s.lo+b.j.lo := by omega
    rw [checkBox,if_neg possible] at pass
    have hc := clip_contains h hsj
    by_cases small : b.clip.upper < 1
    · exact (upper_sound _ _ _ _ hc hsj).trans_lt (by exact_mod_cast small)
    · simp only [small,if_false,Bool.and_eq_true] at pass
      rcases split_cover hc with left | right
      · exact ih _ left pass.1
      · exact ih _ right pass.2

end HadwigerNelson.Certificate.ParameterBoxes

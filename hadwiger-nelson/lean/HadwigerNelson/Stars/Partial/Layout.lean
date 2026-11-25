import HadwigerNelson.Stars.Partial.LayoutRuntime
import HadwigerNelson.Stars.Partial.Colour
import HadwigerNelson.Stars.SourceArea

namespace HadwigerNelson.Stars.PartialCheck.Layout
open BoxCheck (Source InSource physicalSource disjointBox disjointBox_sound)

private structure Valid (i : Nat) : Prop where
  x : (source i).xlo < (source i).xhi
  y : (source i).ylo < (source i).yhi
  xlo : (region (family i)).xlo ≤ (source i).xlo
  xhi : (source i).xhi ≤ (region (family i)).xhi
  ylo : (region (family i)).ylo ≤ (source i).ylo
  yhi : (source i).yhi ≤ (region (family i)).yhi
  low : rowStart (family i) ((i-base (family i))/lanes (family i)) ≤ axisLo (family i) (source i)
  high : axisHi (family i) (source i) ≤
    rowStart (family i) ((i-base (family i))/lanes (family i)) + rowWidth (family i)
  other : (source i).other = alternate (family i)
  colour : classify (source i).box 1 = .inside
  same : ∀ k < lanes (family i), k ≠ (i-base (family i))%lanes (family i) →
    separate (source i) (source (((i-base (family i))/lanes (family i))*lanes (family i) + base (family i)+k)) = true

private theorem valid {i : Nat} (h : entry i = true) : Valid i := by
  simp only [entry,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨x,y⟩,⟨⟨⟨xl,xh⟩,yl⟩,yh⟩⟩,lo,hi⟩,col,inside⟩,rows⟩ := h
  refine ⟨x,y,xl,xh,yl,yh,lo,hi,col,inside,?_⟩
  intro k hk ne
  have h := Array.all_eq_true.mp rows k (by simpa using hk)
  simpa [ne] using h

private theorem in_region {i : Nat} (v : Valid i) {x y : ℝ} (h : InSource (source i) x y) :
    InSource (region (family i)) x y :=
  ⟨(Int.cast_le.mpr v.xlo).trans_lt h.1,h.2.1.trans_le (Int.cast_le.mpr v.xhi),
    (Int.cast_le.mpr v.ylo).trans_lt h.2.2.1,h.2.2.2.trans_le (Int.cast_le.mpr v.yhi)⟩

private theorem region_apart (f g : Family) (h : f ≠ g) :
    separate (region f) (region g) = true := by
  cases f <;> cases g <;> first | contradiction | decide

private theorem increasing (f : Family) (a b : Nat) (hab : a < b) :
    rowStart f a + rowWidth f ≤ rowStart f b := by
  cases f <;> simp only [rowStart,rowWidth] <;> omega

private theorem base_le (i : Nat) : base (family i) ≤ i := by
  unfold family
  split <;> first | exact Nat.zero_le _ | (split <;> first | (change 124995 ≤ _; omega) | (split <;> first | (change 128531 ≤ _; omega) | (change 132621 ≤ _; omega)))

private theorem apart {i j : Nat} (v : Valid i) (w : Valid j) (ne : i ≠ j)
    {x y : ℝ} (a : InSource (source i) x y) (b : InSource (source j) x y) : False := by
  by_cases sameFamily : family i = family j
  · let f := family i
    have fj : family j = f := sameFamily.symm
    let n := lanes f
    let t := i-base f
    let u := j-base f
    have count : 0<n := by dsimp [n]; cases f <;> decide
    have ri : t/n*n + base f + t%n = i := by
      have h := Nat.div_add_mod t n
      rw [Nat.mul_comm n (t/n)] at h
      have baseI : base f ≤ i := base_le i
      dsimp only [t] at h ⊢
      omega
    have rj : u/n*n + base f + u%n = j := by
      have h := Nat.div_add_mod u n
      rw [Nat.mul_comm n (u/n)] at h
      have baseJ : base f ≤ j := fj ▸ base_le j
      dsimp only [u] at h ⊢
      omega
    by_cases rows : t/n = u/n
    · have hn : u%n ≠ t%n := by intro e; rw [rows,←e] at ri; omega
      have cut := v.same (u%n) (Nat.mod_lt _ count) hn
      change separate (source i) (source (t/n*n + base f + u%n)) = true at cut
      rw [rows,rj] at cut
      exact disjointBox_sound cut a b
    · have il := v.low
      have ih := v.high
      have jl := w.low
      have jh := w.high
      rw [fj] at jl jh
      change rowStart f (t/n) ≤ axisLo f (source i) at il
      change axisHi f (source i) ≤ rowStart f (t/n)+rowWidth f at ih
      change rowStart f (u/n) ≤ axisLo f (source j) at jl
      change axisHi f (source j) ≤ rowStart f (u/n)+rowWidth f at jh
      have cut : axisHi f (source i) ≤ axisLo f (source j) ∨
          axisHi f (source j) ≤ axisLo f (source i) := by
        rcases lt_or_gt_of_ne rows with h|h
        · exact Or.inl (ih.trans ((increasing _ _ _ h).trans jl))
        · exact Or.inr (jh.trans ((increasing _ _ _ h).trans il))
      apply disjointBox_sound (a := source i) (b := source j) _ a b
      simp only [disjointBox,Bool.or_eq_true,decide_eq_true_eq]
      by_cases h : f = .bottom <;> simp [axisHi,axisLo,h] at cut <;> tauto
  · exact disjointBox_sound (region_apart _ _ sameFamily) (in_region v a) (in_region w b)

private theorem half {i : Nat} (v : Valid i) :
    physicalSource (source i) ⊆ Wave.halfTile PartialWave.datum false := by
  intro z hz
  have region_limits (f : Family) : 0 ≤ (region f).xlo ∧ (region f).xhi ≤ 1000000 ∧
      0 ≤ (region f).ylo ∧ (region f).yhi ≤ 250000 := by cases f <;> decide
  obtain ⟨l,r,b,t⟩ := region_limits (family i)
  have xl : 0 ≤ ((source i).xlo : ℝ) := by exact_mod_cast l.trans v.xlo
  have xr : ((source i).xhi : ℝ) ≤ 1000000 := by exact_mod_cast v.xhi.trans r
  have yb : 0 ≤ ((source i).ylo : ℝ) := by exact_mod_cast b.trans v.ylo
  have yt : ((source i).yhi : ℝ) ≤ 250000 := by exact_mod_cast v.yhi.trans t
  obtain ⟨h1,h2,h3,h4⟩ := hz
  have hx : 0 ≤ z 0 ∧ z 0 ≤ 1 := ⟨by linarith,by linarith⟩
  have hy : 0 ≤ z 1 ∧ z 1 < Wave.H/2 := by unfold Wave.H; constructor <;> linarith
  have inp := BoxCheck.source_in_box (s := source i) (z := z) ⟨h1,h2,h3,h4⟩
  simp only [CompleteWave.scale,Nat.cast_pow,Nat.cast_ofNat] at inp
  have window : -(2*10^12) ≤ 10^12*z 0 ∧ 10^12*z 0 ≤ 2*10^12 := by constructor <;> linarith [hx.1,hx.2]
  have color := (hasCode_iff_colour 1 (by decide) z).1 ((classify_sound _ 1 _ _ inp window).1 v.colour)
  refine ⟨Placement.first_colour_in_rectangle PartialWave.datum z ⟨hx.1,?_⟩ ⟨hy.1,?_⟩ color,hy.2⟩
  · linarith [PartialWave.datum.x_bounds.1,hx.2]
  · linarith [Wave.H_pos,hy.2]

/-- Real geometric content of the finite source-layout check. -/
structure Physical : Prop where
  subset (i : Fin 136743) : physicalSource (source i.val) ⊆ Wave.halfTile PartialWave.datum false
  disjoint {i j : Fin 136743} (ne : i ≠ j) :
    Disjoint (physicalSource (source i.val)) (physicalSource (source j.val))
  widths (i : Fin 136743) : (source i.val).xlo < (source i.val).xhi ∧ (source i.val).ylo < (source i.val).yhi
  other (i : Fin 136743) : (source i.val).other = alternate (family i.val)

/-- A passing computation certifies containment in the first lower half-tile
and pairwise disjointness of all 136,743 open physical rectangles. -/
theorem check_physical (pass : check = true) : Physical := by
  have v (i : Fin 136743) : Valid i.val := by
    apply valid
    have h := Array.all_eq_true.mp pass i.val (by simp)
    simpa using h
  exact ⟨fun i => half (v i),fun ne => Set.disjoint_left.mpr (fun _ a b =>
    apart (v _) (v _) (Fin.val_ne_of_ne ne) a b),fun i => ⟨(v i).x,(v i).y⟩,fun i => (v i).other⟩

end HadwigerNelson.Stars.PartialCheck.Layout

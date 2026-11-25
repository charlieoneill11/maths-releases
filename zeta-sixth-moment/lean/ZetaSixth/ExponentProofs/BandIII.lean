import ZetaSixth.ExponentProofs.Splits
import ZetaSixth.Native.ExponentCertificates

namespace ZetaSixth.Exponents

namespace CertificateSystems

open Farkas

/-- The real tuple used to interpret the certificate's twelve coordinates. -/
private def assignment (q : Degrees) (δ : ℝ) (k : Fin 12) : ℝ :=
  match k.val with
  | 0 => q.ς
  | 1 => q.g
  | 2 => q.r
  | 3 => q.tail
  | 4 => q.i
  | 5 => q.z
  | 6 => q.x
  | 7 => q.E
  | 8 => q.m
  | 9 => q.n
  | 10 => q.w
  | _ => δ

section Evaluation

variable (q : Degrees) (δ : ℝ)

@[simp] private theorem eval_s : s.eval (assignment q δ) = q.ς := by
  rw [s, Affine.eval_var]
  rfl

@[simp] private theorem eval_g : g.eval (assignment q δ) = q.g := by
  rw [g, Affine.eval_var]
  rfl

@[simp] private theorem eval_r : r.eval (assignment q δ) = q.r := by
  rw [r, Affine.eval_var]
  rfl

@[simp] private theorem eval_tail : tail.eval (assignment q δ) = q.tail := by
  rw [tail, Affine.eval_var]
  rfl

@[simp] private theorem eval_i : i.eval (assignment q δ) = q.i := by
  rw [i, Affine.eval_var]
  rfl

@[simp] private theorem eval_z : z.eval (assignment q δ) = q.z := by
  rw [z, Affine.eval_var]
  rfl

@[simp] private theorem eval_x : x.eval (assignment q δ) = q.x := by
  rw [x, Affine.eval_var]
  rfl

@[simp] private theorem eval_E : E.eval (assignment q δ) = q.E := by
  rw [E, Affine.eval_var]
  rfl

@[simp] private theorem eval_m : m.eval (assignment q δ) = q.m := by
  rw [m, Affine.eval_var]
  rfl

@[simp] private theorem eval_n : n.eval (assignment q δ) = q.n := by
  rw [n, Affine.eval_var]
  rfl

@[simp] private theorem eval_w : w.eval (assignment q δ) = q.w := by
  rw [w, Affine.eval_var]
  rfl

@[simp] private theorem eval_slack : slack.eval (assignment q δ) = δ := by
  rw [slack, Affine.eval_var]
  rfl

@[simp] private theorem eval_sigma : sigma.eval (assignment q δ) = q.sigma := by
  simp [sigma, Degrees.sigma]

@[simp] private theorem eval_tau : tau.eval (assignment q δ) = q.tau := by
  simp [tau, Degrees.tau]

@[simp] private theorem eval_D : D.eval (assignment q δ) = q.lambda + q.i := by
  simp [D, Degrees.lambda]

@[simp] private theorem eval_j (hD : q.D = q.lambda + q.i) :
    j.eval (assignment q δ) = q.j := by
  simp [j, ← hD, Degrees.D]
  ring

@[simp] private theorem eval_a :
    a.eval (assignment q δ) = q.a := by
  simp [a, Degrees.a]

@[simp] private theorem eval_b :
    b.eval (assignment q δ) = q.b := by
  simp [b, Degrees.b]

@[simp] private theorem eval_Z :
    Z.eval (assignment q δ) = q.Z := by
  simp [Z, Degrees.Z]

@[simp] private theorem eval_y (hD : q.D = q.lambda + q.i) :
    y.eval (assignment q δ) = q.y := by
  simp [y, Degrees.y, hD]

@[simp] private theorem eval_C :
    C.eval (assignment q δ) = q.C := by
  simp [C, Degrees.C]

@[simp] private theorem eval_u (hD : q.D = q.lambda + q.i) :
    u.eval (assignment q δ) = q.u := by
  simp [u, Degrees.u, hD]

@[simp] private theorem eval_splitBudget :
    splitBudget.eval (assignment q δ) = q.splitBudget := by
  simp [splitBudget, Degrees.splitBudget]

@[simp] private theorem eval_budget (hD : q.D = q.lambda + q.i) :
    budget.eval (assignment q δ) = q.budget := by
  simp [budget, Degrees.budget, hD]

@[simp] private theorem eval_c :
    c.eval (assignment q δ) = q.c := by
  simp [c, Degrees.c]

@[simp] private theorem eval_d :
    d.eval (assignment q δ) = q.d := by
  simp [d, Degrees.d]

@[simp] private theorem eval_R :
    R.eval (assignment q δ) = q.R := by
  simp [R, Degrees.R]

@[simp] private theorem eval_N (hD : q.D = q.lambda + q.i) :
    N.eval (assignment q δ) = q.N := by
  simp [N, Degrees.N, hD]

@[simp] private theorem eval_J :
    J.eval (assignment q δ) = q.J := by
  simp [J, Degrees.J]

@[simp] private theorem eval_level :
    level.eval (assignment q δ) = q.level := by
  simp [level, Degrees.level]

@[simp] private theorem eval_exceptional (hD : q.D = q.lambda + q.i) :
    exceptional.eval (assignment q δ) = q.exceptional := by
  simp [exceptional, Degrees.exceptional, hD]
  ring

/-- The cap on the mark in each of the five batches of Section 2 of the released checker. -/
noncomputable def Band.realCap (band : Band) (q : Degrees) : ℝ :=
  match band with
  | .completionLow => (13 - 47 * q.ς) / 30
  | .completionHigh => (7 - 19 * q.ς) / 30
  | .representedLow => (2 - 7 * q.ς) / 4
  | .representedMiddle => (1 - 2 * q.ς) / 4
  | .representedHigh => (1 - 3 * q.ς) / 2

@[simp] private theorem eval_cap (band : Band) :
    band.cap.eval (assignment q δ) = band.realCap q := by
  cases band <;> simp [Band.cap, Band.realCap] <;> ring

private theorem eval_directOptions (hD : q.D = q.lambda + q.i) :
    directOptions.map (Affine.eval (assignment q δ)) =
      q.directTerms.map (fun term => -q.directMargin term 0) := by
  simp [directOptions, Degrees.directTerms, Degrees.directMargin, hD, neg_sub]

private theorem eval_levelRow (hD : q.D = q.lambda + q.i)
    (jTerm nTerm exceptionTerm : Bool) :
    (levelRow jTerm nTerm exceptionTerm).eval (assignment q δ) =
      -(2 * q.representedMargin jTerm nTerm exceptionTerm) := by
  cases jTerm <;> cases nTerm <;> cases exceptionTerm <;>
    simp [levelRow, Degrees.representedMargin, Degrees.representedBase, hD] <;> ring

end Evaluation

private theorem domain_nonneg (q : Degrees) (δ : ℝ) (band : Band) (hq : q.Admissible)
    (hς : 0 < q.ς) (hδ : 0 < δ) (ht : ¬ q.Trivial) (hn : ¬ q.Unsigned)
    (hw : q.w ≤ 1 / 2) (hJ : band.represented = true → 0 ≤ q.J)
    (hLow : (band.lower : ℝ) ≤ q.ς) (hHigh : q.ς + δ ≤ (band.upper : ℝ))
    (hCap : q.w + δ ≤ band.realCap q) :
    ∀ row ∈ domain band, 0 ≤ row.eval (assignment q δ) := by
  rcases hq with ⟨hg, hr, hi, hv, _, hDual, hOrder, hiMax, hD, hz, hx, hE, hw₀, hy, hEZ, hEa, hwC, _⟩
  obtain ⟨h43, h32, h21⟩ := q.dual_order hOrder
  have h23 : q.j = q.dual 2 + q.dual 3 := rfl
  have hm : 0 ≤ q.m := hDual 0
  have hn₀ : 0 ≤ q.n := hDual 1
  have ht₀ := q.tau_nonneg_of_not_trivial ht
  have hu := q.u_nonneg_of_not_trivial ht
  have hmMax := q.m_le_of_not_unsigned hn
  intro row hrow
  simp only [domain, List.mem_append] at hrow
  rcases hrow with (hrow | hrow) | hrow
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · simpa using hς.le
    · simpa using hg
    · simpa using hr
    · simpa using hv
    · simpa using hi
    · simpa using hz
    · simpa using hx
    · simpa using hE
    · simpa using hm
    · simpa using hn₀
    · simpa using hw₀
    · simpa using hδ.le
    · simpa using ht₀
    · simpa using hiMax
    · simpa using h21
    · simp only [Affine.eval_sub, Affine.eval_nsmul, eval_n, eval_j q δ hD, Nat.cast_ofNat]
      linarith only [h23, h43, h32]
    · simpa [hD] using hy
    · simpa using hEZ
    · simpa using hEa
    · simpa using hwC
    · simpa using hw
    · simpa using hmMax
    · simpa [hD] using hu
  · by_cases h : band.represented = true
    · simp [h] at hrow
      subst row
      simpa using hJ h
    · simp [h] at hrow
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl
    · simpa using hLow
    · simp only [Affine.eval_sub, Affine.eval_const, eval_s, eval_slack]
      linarith only [hHigh]
    · simp only [Affine.eval_sub, eval_cap, eval_w, eval_slack]
      linarith only [hCap]

private theorem split_nonneg (q : Degrees) (δ : ℝ) (band : Band) (hq : q.Admissible)
    (hHigh : q.ς < (band.upper : ℝ)) (hn : ¬ q.Unsigned) :
    ∃ rows ∈ splitOptions band, ∀ row ∈ rows, 0 ≤ row.eval (assignment q δ) := by
  rcases hq with ⟨hg, hr, _, hv, hσ₀, _, _, _, hD, _⟩
  by_cases hσ : 4 * q.tau < q.sigma
  · have hPair : ∃ row ∈ pairOptions, 0 ≤ row.eval (assignment q δ) := by
      rcases q.first_pair_split_failure hn hσ hσ₀ with h | h
      · refine ⟨2 • tau - j, by simp [pairOptions], ?_⟩
        simpa [hD] using h
      · refine ⟨splitBudget - m - n, by simp [pairOptions], ?_⟩
        simp only [Affine.eval_sub, eval_splitBudget, eval_m, eval_n]
        linarith only [h]
    have hSingle : ∃ row ∈ singleOptions, 0 ≤ row.eval (assignment q δ) := by
      rcases q.singleton_split_failure hn hσ with h | h | h
      · exact ⟨2 • tau - m, by simp [singleOptions], by simpa using h⟩
      · exact ⟨2 • tau - (D - m), by simp [singleOptions], by simpa [← hD] using h⟩
      · exact ⟨splitBudget - (D - m), by simp [singleOptions], by simpa [← hD] using h⟩
    obtain ⟨pair, hpair, hPair⟩ := hPair
    obtain ⟨single, hsingle, hSingle⟩ := hSingle
    refine ⟨[pair, single], ?_, ?_⟩
    · exact List.mem_append_left _ <|
        List.mem_flatMap.mpr ⟨pair, hpair, List.mem_map.mpr ⟨single, hsingle, rfl⟩⟩
    · intro row hrow
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl | rfl
      · exact hPair
      · exact hSingle
  · have hBand : band = .representedHigh := by
      cases band
      all_goals first
        | rfl
        | exfalso
          apply hσ
          apply q.four_tau_lt_sigma _ hg hr hv
          norm_num [Band.upper] at hHigh
          linarith only [hHigh]
    refine ⟨[4 • tau - sigma], by simp [splitOptions, hBand], ?_⟩
    intro row hrow
    have hr' : row = 4 • tau - sigma := by simpa using hrow
    subst row
    simpa using le_of_not_gt hσ

private theorem reciprocal_nonneg (q : Degrees) (δ : ℝ) (hD : q.D = q.lambda + q.i)
    (h : ¬ q.Reciprocal) : ∃ row ∈ reciprocalOptions, 0 ≤ row.eval (assignment q δ) := by
  by_cases hLeft : 0 < q.C / 2 - q.u
  · refine ⟨u + C / 2 - b, by simp [reciprocalOptions], ?_⟩
    have hRight : q.b - q.C / 2 - q.u ≤ 0 := le_of_not_gt fun hs => h ⟨hLeft, hs⟩
    simp only [Affine.eval_sub, Affine.eval_add, Affine.eval_natDiv, eval_u q δ hD,
      eval_C, eval_b, Nat.cast_ofNat]
    linarith only [hRight]
  · refine ⟨u - C / 2, by simp [reciprocalOptions], ?_⟩
    simp only [Affine.eval_sub, Affine.eval_natDiv, eval_u q δ hD, eval_C, Nat.cast_ofNat]
    linarith only [le_of_not_gt hLeft]

private theorem failed_direct_term (q : Degrees) (gain : ℝ)
    (h : ¬ ∀ term ∈ q.directTerms, 0 < q.directMargin term gain) :
    ∃ term ∈ q.directTerms, q.directMargin term gain ≤ 0 := by
  by_contra hn
  apply h
  intro term hm
  exact lt_of_not_ge (fun hs => hn ⟨term, hm, hs⟩)

private theorem direct_nonneg (q : Degrees) (δ : ℝ) (band : Band) (hD : q.D = q.lambda + q.i)
    (h : ¬ q.Direct) (hGain : band.represented = true → ¬ q.DirectWithGain) :
    ∃ row ∈ directOptions, 0 ≤ row.eval (assignment q δ) ∧
      (band.represented = true → 0 ≤ (row - E + z).eval (assignment q δ)) := by
  have hTerm : ∃ term ∈ q.directTerms, q.directMargin term 0 ≤ 0 ∧
      (band.represented = true → q.directMargin term (q.E - q.z) ≤ 0) := by
    by_cases hBand : band.represented = true
    · by_cases hGainSign : 0 ≤ q.E - q.z
      · obtain ⟨term, hterm, hm⟩ :=
          failed_direct_term q (q.E - q.z) (fun h' => hGain hBand (Or.inr h'))
        refine ⟨term, hterm, ?_, fun _ => hm⟩
        unfold Degrees.directMargin at hm ⊢
        linarith only [hm, hGainSign]
      · obtain ⟨term, hterm, hm⟩ := failed_direct_term q 0 h
        refine ⟨term, hterm, hm, fun _ => ?_⟩
        unfold Degrees.directMargin at hm ⊢
        linarith only [hm, le_of_not_ge hGainSign]
    · obtain ⟨term, hterm, hm⟩ := failed_direct_term q 0 h
      exact ⟨term, hterm, hm, fun h' => (hBand h').elim⟩
  obtain ⟨term, hterm, hNoDirect, hNoGain⟩ := hTerm
  have hmem : -q.directMargin term 0 ∈ directOptions.map (Affine.eval (assignment q δ)) := by
    rw [eval_directOptions q δ hD]
    exact List.mem_map.mpr ⟨term, hterm, rfl⟩
  obtain ⟨row, hrow, hv⟩ := List.mem_map.mp hmem
  refine ⟨row, hrow, by rw [hv]; exact neg_nonneg.mpr hNoDirect, fun hBand => ?_⟩
  simp only [Affine.eval_add, Affine.eval_sub, eval_E, eval_z, hv]
  have hNoGain := hNoGain hBand
  unfold Degrees.directMargin at hNoGain ⊢
  linarith only [hNoGain]

private theorem level_nonneg (q : Degrees) (δ : ℝ) (hD : q.D = q.lambda + q.i)
    (h : ¬ q.RepresentedLevel) :
    0 ≤ q.J ∧ ∃ row ∈ levelOptions, 0 ≤ row.eval (assignment q δ) := by
  refine ⟨neg_nonpos.mp (le_of_not_gt fun hj => h (Or.inl hj)), ?_⟩
  have hFail : ∃ j n e : Bool, q.representedMargin j n e ≤ 0 := by
    by_contra hc
    exact h (Or.inr fun j n e => lt_of_not_ge fun hm => hc ⟨j, n, e, hm⟩)
  obtain ⟨j, n, e, hMargin⟩ := hFail
  refine ⟨levelRow j n e, ?_, ?_⟩
  · cases j <;> cases n <;> cases e <;> simp [levelOptions]
  · rw [eval_levelRow q δ hD]
    linarith only [hMargin]

/-- Transfer the checked rational systems of one band to real degree tuples. -/
private theorem exclude_uncovered (band : Band) (data : String)
    (checked : Farkas.checkEncoded slack (systems band) data = true)
    (q : Degrees) (hq : q.Admissible) (hς : 0 < q.ς)
    (hLow : (band.lower : ℝ) ≤ q.ς) (hHigh : q.ς < (band.upper : ℝ))
    (hMark : q.mark < band.realCap q) (ht : ¬ q.Trivial) (hu : ¬ q.Unsigned)
    (hr : ¬ q.Reciprocal) (hd : ¬ q.Direct)
    (hg : band.represented = true → ¬ q.DirectWithGain)
    (hl : band.represented = true → ¬ q.RepresentedLevel) : False := by
  have hD : q.D = q.lambda + q.i := by
    rcases hq with ⟨_, _, _, _, _, _, _, _, hD, _⟩
    exact hD
  have hwMark : q.w ≤ q.mark := by
    rcases hq with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hle⟩
    exact hle
  have hCap : q.w < band.realCap q := lt_of_le_of_lt hwMark hMark
  have hHalf : band.realCap q ≤ 1 / 2 := by
    cases band <;> unfold Band.realCap <;> linarith only [hς]
  let δ := min ((band.upper : ℝ) - q.ς) (band.realCap q - q.w)
  have hPos : 0 < δ :=
    lt_min (sub_pos.mpr hHigh) (sub_pos.mpr hCap)
  have hδUpper : q.ς + δ ≤ (band.upper : ℝ) := by
    have h := min_le_left ((band.upper : ℝ) - q.ς) (band.realCap q - q.w)
    change δ ≤ (band.upper : ℝ) - q.ς at h
    linarith only [h]
  have hδCap : q.w + δ ≤ band.realCap q := by
    have h := min_le_right ((band.upper : ℝ) - q.ς) (band.realCap q - q.w)
    change δ ≤ band.realCap q - q.w at h
    linarith only [h]
  have hDmn := domain_nonneg q δ band hq hς hPos ht hu (hCap.le.trans hHalf)
    (fun hb => (level_nonneg q δ hD (hl hb)).1) hLow hδUpper hδCap
  obtain ⟨split, hsplit, hSplit⟩ := split_nonneg q δ band hq hHigh hu
  obtain ⟨reciprocal, hrecip, hRecip⟩ := reciprocal_nonneg q δ hD hr
  obtain ⟨direct, hdir, hDirect, hWithGain⟩ := direct_nonneg q δ band hD hd hg
  by_cases hb : band.represented = true
  · obtain ⟨represented, hlevel, hLevel⟩ := (level_nonneg q δ hD (hl hb)).2
    have hmem : domain band ++ split ++ [reciprocal, direct, direct - E + z, represented] ∈
        systems band := by
      unfold systems
      rw [List.mem_flatMap]
      refine ⟨split, hsplit, List.mem_flatMap.mpr ⟨reciprocal, hrecip, ?_⟩⟩
      apply List.mem_flatMap.mpr
      refine ⟨direct, hdir, ?_⟩
      simp only [hb, if_true]
      exact List.mem_map.mpr ⟨represented, hlevel, rfl⟩
    apply Farkas.checkEncoded_sound checked hmem (assignment q δ) _ (by simpa using hPos)
    intro row hrow
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with (h | h) | rfl | rfl | rfl | rfl
    · exact hDmn row h
    · exact hSplit row h
    · exact hRecip
    · exact hDirect
    · exact hWithGain hb
    · exact hLevel
  · have hmem : domain band ++ split ++ [reciprocal, direct] ∈ systems band := by
      unfold systems
      rw [List.mem_flatMap]
      refine ⟨split, hsplit, List.mem_flatMap.mpr ⟨reciprocal, hrecip, ?_⟩⟩
      apply List.mem_flatMap.mpr
      exact ⟨direct, hdir, by simp [hb]⟩
    apply Farkas.checkEncoded_sound checked hmem (assignment q δ) _ (by simpa using hPos)
    intro row hrow
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with (h | h) | rfl | rfl
    · exact hDmn row h
    · exact hSplit row h
    · exact hRecip
    · exact hDirect

private theorem represented_saves (band : Band) (data : String)
    (checked : Farkas.checkEncoded slack (systems band) data = true)
    (q : Degrees) (hq : q.Admissible) (hς : 0 < q.ς)
    (hLow : (band.lower : ℝ) ≤ q.ς) (hHigh : q.ς < (band.upper : ℝ))
    (hMark : q.mark < band.realCap q) :
    q.Trivial ∨ q.Unsigned ∨ q.Reciprocal ∨ q.DirectWithGain ∨ q.RepresentedLevel := by
  by_cases hTriv : q.Trivial
  · exact Or.inl hTriv
  by_cases hUn : q.Unsigned
  · exact Or.inr (Or.inl hUn)
  by_cases hRec : q.Reciprocal
  · exact Or.inr (Or.inr (Or.inl hRec))
  by_cases hDir : q.DirectWithGain
  · exact Or.inr (Or.inr (Or.inr (Or.inl hDir)))
  by_cases hLev : q.RepresentedLevel
  · exact Or.inr (Or.inr (Or.inr (Or.inr hLev)))
  exact (exclude_uncovered band data checked q hq hς hLow hHigh hMark hTriv hUn hRec
    (fun h => hDir (Or.inl h)) (fun _ => hDir) (fun _ => hLev)).elim

private theorem completion_saves (band : Band) (data : String)
    (checked : Farkas.checkEncoded slack (systems band) data = true) (hb : band.represented = false)
    (q : Degrees) (hq : q.Admissible) (hς : 0 < q.ς)
    (hLow : (band.lower : ℝ) ≤ q.ς) (hHigh : q.ς < (band.upper : ℝ))
    (hMark : q.mark < band.realCap q) :
    q.Trivial ∨ q.Unsigned ∨ q.Reciprocal ∨ q.Direct := by
  by_cases hTriv : q.Trivial
  · exact Or.inl hTriv
  by_cases hUn : q.Unsigned
  · exact Or.inr (Or.inl hUn)
  by_cases hRec : q.Reciprocal
  · exact Or.inr (Or.inr (Or.inl hRec))
  by_cases hDir : q.Direct
  · exact Or.inr (Or.inr (Or.inr hDir))
  have hNo (h : band.represented = true) : False := by rw [hb] at h; contradiction
  exact (exclude_uncovered band data checked q hq hς hLow hHigh hMark hTriv hUn hRec hDir
    (fun h => (hNo h).elim) (fun h => (hNo h).elim)).elim

end CertificateSystems

open CertificateSystems

/-- Lemma 90(iii), backed by the three checked represented-level batches. -/
theorem bandIII_saves (q : Degrees) (hq : q.Admissible) (hς : 0 < q.ς) (h : q.BandIII) :
    q.Trivial ∨ q.Unsigned ∨ q.Reciprocal ∨ q.DirectWithGain ∨ q.RepresentedLevel := by
  rcases h with ⟨hl, hu, hm⟩ | ⟨hl, hu, hm⟩ | ⟨hl, hu, hm⟩
  · apply CertificateSystems.represented_saves .representedLow _ NativeCertificates.representedLow
      q hq hς
    · simpa [Band.lower] using hl
    · simpa [Band.upper] using hu
    · exact hm
  · apply CertificateSystems.represented_saves .representedMiddle _
      NativeCertificates.representedMiddle q hq hς
    · simpa [Band.lower] using hl
    · simpa [Band.upper] using hu
    · exact hm
  · apply CertificateSystems.represented_saves .representedHigh _ NativeCertificates.representedHigh
      q hq hς
    · simpa [Band.lower] using hl
    · simpa [Band.upper] using hu
    · exact hm

/-- The two narrower mark bands in the remark following Lemma 90. -/
theorem completion_only_saves (q : Degrees) (hq : q.Admissible) (hς : 0 < q.ς)
    (h :
      (1 / 10 ≤ q.ς ∧ q.ς < 1 / 7 ∧ q.mark < (13 - 47 * q.ς) / 30) ∨
      (1 / 7 ≤ q.ς ∧ q.ς < 1 / 4 ∧ q.mark < (7 - 19 * q.ς) / 30)) :
    q.Trivial ∨ q.Unsigned ∨ q.Reciprocal ∨ q.Direct := by
  rcases h with ⟨hl, hu, hm⟩ | ⟨hl, hu, hm⟩
  · apply CertificateSystems.completion_saves .completionLow _ NativeCertificates.completionLow
      rfl q hq hς
    · simpa [Band.lower] using hl
    · simpa [Band.upper] using hu
    · exact hm
  · apply CertificateSystems.completion_saves .completionHigh _ NativeCertificates.completionHigh
      rfl q hq hς
    · simpa [Band.lower] using hl
    · simpa [Band.upper] using hu
    · exact hm

end ZetaSixth.Exponents

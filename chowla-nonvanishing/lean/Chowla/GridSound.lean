import Chowla.CheckerGrid
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.FieldSimp

namespace Chowla.Checker

open scoped BigOperators

private theorem ratGrid_pos : 0 < (grid : ℚ) := by norm_num [grid]
private theorem ratGrid_ne_zero : (grid : ℚ) ≠ 0 := ne_of_gt ratGrid_pos

/-- Apply a linear functional to the coefficient vector at an integer-grid knot. -/
def GridJet.weighted (jet : GridJet) (f : ℤ → ℕ → ℚ) : ℚ :=
  ∑ j ∈ Finset.range jet.coefficients.size, (jet.coefficients[j]?.getD 0 : ℚ) * f jet.knot j

private def weightedJets (jets : List GridJet) (f : ℤ → ℕ → ℚ) : ℚ :=
  (jets.map (fun jet => jet.weighted f)).sum

private def weightedSpline (p : Spline) (f : ℚ → ℕ → ℚ) : ℚ :=
  (p.map fun t => t.coefficient * f t.knot t.degree).sum

/-- Integer jets represent a rational spline after dividing each knot by the grid
and restoring the grid powers and common denominator of the coefficients. -/
def GridSpline.Represents (q : GridSpline) (p : Spline) : Prop :=
  q.denominator ≠ 0 ∧ (∀ jet ∈ q.jets, jet.coefficients.size ≤ q.degree + 1) ∧
    ∀ f : ℚ → ℕ → ℚ,
      weightedSpline p f =
        weightedJets q.jets (fun k j => (grid : ℚ) ^ j * f ((k : ℚ) / grid) j) / q.denominator

private theorem foldl_add_eq_sum_map {α R : Type*} [AddCommMonoid R]
    (f : α → R) (xs : List α) (a : R) :
    xs.foldl (fun acc x => acc + f x) a = a + (xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih, add_assoc]

private theorem intCast_sum_map {α : Type*} (f : α → ℤ) (xs : List α) :
    ((xs.map f).sum : ℚ) = (xs.map (fun t => (f t : ℚ))).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem weightedJet_mul (p : GridJet) (c : ℚ) (f : ℤ → ℕ → ℚ) :
    p.weighted (fun k j => c * f k j) = c * p.weighted f := by
  unfold GridJet.weighted
  rw [Finset.mul_sum]
  congr 1
  ext
  ring

private theorem weightedJets_mul (jets : List GridJet) (c : ℚ) (f : ℤ → ℕ → ℚ) :
    weightedJets jets (fun k j => c * f k j) = c * weightedJets jets f := by
  induction jets with
  | nil => simp [weightedJets]
  | cons jet jets ih =>
    simp only [weightedJets, List.map_cons, List.sum_cons, weightedJet_mul] at ih ⊢
    rw [ih, mul_add]

private theorem list_horner (as : List ℤ) (x : ℤ) :
    ((as.foldr (fun c rest => c + x * rest) 0 : ℤ) : ℚ) =
      ∑ j ∈ Finset.range as.length, (as[j]?.getD 0 : ℚ) * (x : ℚ) ^ j := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldr_cons, List.length_cons, Int.cast_add, Int.cast_mul, ih]
    rw [Finset.sum_range_succ']
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, pow_zero, mul_one]
    rw [Finset.mul_sum]
    rw [add_comm (a : ℚ)]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    ring

private theorem array_horner (as : Array ℤ) (x : ℤ) :
    ((as.foldr (fun c rest => c + x * rest) 0 : ℤ) : ℚ) =
      ∑ j ∈ Finset.range as.size, (as[j]?.getD 0 : ℚ) * (x : ℚ) ^ j := by
  simpa only [Array.foldr_toList, Array.length_toList, Array.getElem?_toList] using
    list_horner as.toList x

private def primitiveWeight (x : ℤ) (n : ℕ) (k : ℤ) (j : ℕ) : ℚ :=
  if k ≤ x then (↑(x - k) : ℚ) ^ (j + n) / (j + n).factorial else 0

private theorem primitive_scaled_term (degree n : ℕ) (jet : GridJet)
    (hdegree : jet.coefficients.size ≤ degree + 1) (x : ℤ) :
    ((if x - jet.knot < 0 then 0 else
      (jet.coefficients.mapIdx fun j (c : ℤ) => c * ((degree + n).factorial / (j + n).factorial : ℕ)).foldr
        (fun c rest => c + (x - jet.knot) * rest) 0 * (x - jet.knot)^n : ℤ) : ℚ) =
      ((degree + n).factorial : ℚ) * jet.weighted (primitiveWeight x n) := by
  by_cases hx : jet.knot ≤ x
  · have hno : ¬ x - jet.knot < 0 := not_lt_of_ge (sub_nonneg.mpr hx)
    simp only [if_neg hno, Int.cast_mul, Int.cast_pow]
    rw [array_horner]
    simp only [Array.size_mapIdx, GridJet.weighted, primitiveWeight, if_pos hx]
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hdiv : (j+n).factorial ∣ (degree+n).factorial :=
      Nat.factorial_dvd_factorial (by omega)
    have hnonzero : ((j+n).factorial : ℚ) ≠ 0 := by positivity
    rw [Array.getElem?_mapIdx, Array.getElem?_eq_getElem hj']
    simp only [Option.map_some, Option.getD_some, Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div hdiv hnonzero, pow_add]
    ring
  · have hh : x - jet.knot < 0 := sub_neg.mpr (lt_of_not_ge hx)
    simp [hh, GridJet.weighted, primitiveWeight, hx]

/-- Integer Horner evaluation equals exact truncated-power evaluation at the same
grid point, with the factorial multiplier and grid rescaling accounted for. -/
theorem GridSpline.primitive_eval_weighted (p : GridSpline) (hd : p.denominator ≠ 0)
    (hdegree : ∀ jet ∈ p.jets, jet.coefficients.size ≤ p.degree + 1)
    (n : ℕ) (x : ℤ) :
    (p.primitive n).eval x =
      weightedJets p.jets (primitiveWeight x n) / ((p.denominator : ℚ) * (grid : ℚ) ^ n) := by
  unfold GridSpline.primitive GridPrimitive.eval
  simp only [cachedFactorial_eq, List.foldl_map]
  have hfun (acc : ℤ) (jet : GridJet) :
      (if x - jet.knot < 0 then acc else acc +
        (jet.coefficients.mapIdx fun j (c : ℤ) => c *
          ((p.degree + n).factorial / (j + n).factorial : ℕ)).foldr
          (fun c rest => c + (x - jet.knot) * rest) 0 * (x - jet.knot)^n) =
      acc + if x - jet.knot < 0 then 0 else
        (jet.coefficients.mapIdx fun j (c : ℤ) => c *
          ((p.degree + n).factorial / (j + n).factorial : ℕ)).foldr
          (fun c rest => c + (x - jet.knot) * rest) 0 * (x - jet.knot)^n := by
    split_ifs <;> simp
  simp_rw [hfun]
  rw [foldl_add_eq_sum_map, zero_add, intCast_sum_map]
  have hsum :
      (p.jets.map (fun jet => ((if x - jet.knot < 0 then 0 else
        (jet.coefficients.mapIdx fun j (c : ℤ) => c *
          ((p.degree + n).factorial / (j + n).factorial : ℕ)).foldr
          (fun c rest => c + (x - jet.knot) * rest) 0 * (x - jet.knot)^n : ℤ) : ℚ))).sum =
      ((p.degree + n).factorial : ℚ) * weightedJets p.jets (primitiveWeight x n) := by
    unfold weightedJets
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro jet hj
    exact primitive_scaled_term p.degree n jet (hdegree jet hj) x
  rw [hsum]
  push_cast
  have hg : (grid : ℚ) ≠ 0 := ratGrid_ne_zero
  have hden : (p.denominator : ℚ) ≠ 0 := by exact_mod_cast hd
  have hfac : ((p.degree + n).factorial : ℚ) ≠ 0 := by positivity
  field_simp

private def rationalPrimitiveWeight (x : ℚ) (n : ℕ) (k : ℚ) (j : ℕ) : ℚ :=
  if k ≤ x then (x-k) ^ (j + n) / (j + n).factorial else 0

private theorem splinePrimitives_weighted (p : Spline) (n : ℕ) (x : ℚ) :
    splinePrimitives p n x = weightedSpline p (rationalPrimitiveWeight x n) := by
  simp [splinePrimitives, Spline.eval, Spline.primitive, weightedSpline,
    rationalPrimitiveWeight, List.map_map, Function.comp_def]

private theorem weight_rescale (x k : ℤ) (n j : ℕ) :
    (grid : ℚ) ^ j * rationalPrimitiveWeight ((x : ℚ) / grid) n ((k : ℚ) / grid) j =
      ((grid : ℚ) ^ n)⁻¹ * primitiveWeight x n k j := by
  have hsign : (k : ℚ) / grid ≤ (x : ℚ) / grid ↔ k ≤ x := by
    rw [div_le_div_iff_of_pos_right ratGrid_pos]
    exact Int.cast_le
  by_cases hk : k ≤ x
  · simp only [rationalPrimitiveWeight, primitiveWeight, if_pos (hsign.mpr hk), if_pos hk]
    rw [← sub_div, div_pow, pow_add (grid : ℚ) j n]
    push_cast
    have hg := ratGrid_ne_zero
    have hf : ((j + n).factorial : ℚ) ≠ 0 := by positivity
    field_simp
  · simp only [rationalPrimitiveWeight, primitiveWeight, if_neg (hsign.not.mpr hk),
      if_neg hk, mul_zero]

theorem GridSpline.primitive_eval_sound {q : GridSpline} {p : Spline}
    (h : q.Represents p) (n : ℕ) (x : ℤ) :
    (q.primitive n).eval x = splinePrimitives p n ((x : ℚ) / grid) := by
  rw [q.primitive_eval_weighted h.1 h.2.1, splinePrimitives_weighted, h.2.2]
  simp_rw [weight_rescale]
  rw [weightedJets_mul]
  have hden : (q.denominator : ℚ) ≠ 0 := by exact_mod_cast h.1
  have hg := ratGrid_ne_zero
  field_simp

private theorem size_addArrays (a b : Array ℤ) :
    (addArrays a b).size = max a.size b.size := by simp [addArrays]

private theorem getD_addArrays (a b : Array ℤ) (j : ℕ) :
    (addArrays a b)[j]?.getD 0 = a[j]?.getD 0 + b[j]?.getD 0 := by
  by_cases hj : j < max a.size b.size
  · simp only [addArrays, Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hj,
      Option.map_some, Option.getD_some]
  · have ha : a.size ≤ j := (le_max_left ..).trans (le_of_not_gt hj)
    have hb : b.size ≤ j := (le_max_right ..).trans (le_of_not_gt hj)
    have hc : (addArrays a b).size ≤ j := by rw [size_addArrays]; exact le_of_not_gt hj
    simp [Array.getElem?_eq_none ha, Array.getElem?_eq_none hb, Array.getElem?_eq_none hc]

private theorem weightedJet_expand_range (jet : GridJet) (f : ℤ → ℕ → ℚ) {d : ℕ}
    (hd : jet.coefficients.size ≤ d) :
    (∑ j ∈ Finset.range d, (jet.coefficients[j]?.getD 0 : ℚ) * f jet.knot j) = jet.weighted f := by
  symm
  apply Finset.sum_subset (Finset.range_mono hd)
  intro j _ hj
  have hle : jet.coefficients.size ≤ j := le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
  simp [Array.getElem?_eq_none hle]

private theorem weightedJet_addArrays (k : ℤ) (a b : Array ℤ) (f : ℤ → ℕ → ℚ) :
    GridJet.weighted ⟨k, addArrays a b⟩ f = GridJet.weighted ⟨k, a⟩ f +
      GridJet.weighted ⟨k, b⟩ f := by
  change (∑ j ∈ Finset.range (addArrays a b).size,
    ((addArrays a b)[j]?.getD 0 : ℚ) * f k j) = _
  simp_rw [size_addArrays, getD_addArrays, Int.cast_add, add_mul, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·)
    (weightedJet_expand_range ⟨k, a⟩ f (le_max_left ..))
    (weightedJet_expand_range ⟨k, b⟩ f (le_max_right ..))

private theorem weightedJets_addJet (a : GridJet) (bs : List GridJet) (f : ℤ → ℕ → ℚ) :
    weightedJets (addJet a bs) f = a.weighted f + weightedJets bs f := by
  induction bs with
  | nil => simp [addJet, weightedJets]
  | cons b bs ih =>
    by_cases h : a.knot = b.knot
    · simp only [addJet, if_pos h, weightedJets, List.map_cons, List.sum_cons]
      rw [weightedJet_addArrays]
      cases a
      simp only at h ⊢
      subst h
      simp only [add_assoc]
    · simp only [addJet, if_neg h, weightedJets, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ac_rfl

private theorem addJet_degree_bound (d : ℕ) (a : GridJet) (ha : a.coefficients.size ≤ d)
    (bs : List GridJet) (hb : ∀ b ∈ bs, b.coefficients.size ≤ d) :
    ∀ b ∈ addJet a bs, b.coefficients.size ≤ d := by
  induction bs with
  | nil =>
    intro b h
    have he : b = a := by simpa [addJet] using h
    simpa [he] using ha
  | cons b bs ih =>
    have hb' : ∀ q ∈ bs, q.coefficients.size ≤ d := fun q h =>
      hb q (List.mem_cons_of_mem b h)
    have hbb := hb b List.mem_cons_self
    by_cases h : a.knot = b.knot
    · simp only [addJet, if_pos h, List.mem_cons]
      intro q hq
      rcases hq with rfl | hq
      · exact (size_addArrays a.coefficients b.coefficients).le.trans (max_le ha hbb)
      · exact hb' q hq
    · simp only [addJet, if_neg h, List.mem_cons]
      intro q hq
      rcases hq with rfl | hq
      · exact hbb
      · exact ih hb' q hq

private theorem size_singleCoefficient (j : ℕ) (c : ℤ) :
    (singleCoefficient j c).size = j + 1 := by simp [singleCoefficient]

private theorem weightedJet_singleCoefficient (k : ℤ) (j : ℕ) (c : ℤ) (f : ℤ → ℕ → ℚ) :
    GridJet.weighted ⟨k, singleCoefficient j c⟩ f = (c : ℚ) * f k j := by
  change (∑ i ∈ Finset.range (singleCoefficient j c).size,
    ((singleCoefficient j c)[i]?.getD 0 : ℚ) * f k i) = _
  rw [size_singleCoefficient, Finset.sum_eq_single j]
  · simp only [singleCoefficient, Array.getElem?_push, Array.size_replicate, if_true,
      Option.getD_some]
  · intro i _ h
    simp only [singleCoefficient, Array.getElem?_push, Array.size_replicate, if_neg h,
      Array.getElem?_replicate]
    split_ifs <;> simp
  · simp

private theorem foldl_lcm_pos {α : Type*} (den : α → ℕ) (xs : List α)
    (h : ∀ a ∈ xs, 0 < den a) {acc : ℕ} (ha : 0 < acc) :
    0 < xs.foldl (fun d x => d.lcm (den x)) acc := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons x xs ih =>
    apply ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    exact Nat.lcm_pos ha (h x List.mem_cons_self)

private theorem foldl_lcm_dvd (xs : List ℕ) (acc d : ℕ) (h : d ∣ acc ∨ d ∈ xs) :
    d ∣ xs.foldl Nat.lcm acc := by
  induction xs generalizing acc with
  | nil => simpa using h
  | cons x xs ih =>
    refine ih (acc.lcm x) ?_
    rcases h with hd | hm
    · exact Or.inl (hd.trans (Nat.dvd_lcm_left ..))
    · rcases List.mem_cons.mp hm with he | ht
      · subst x
        exact Or.inl (Nat.dvd_lcm_right ..)
      · exact Or.inr ht

private theorem foldl_max_bound (xs : List ℕ) (acc d : ℕ) (h : d ≤ acc ∨ d ∈ xs) :
    d ≤ xs.foldl max acc := by
  induction xs generalizing acc with
  | nil => simpa using h
  | cons x xs ih =>
    refine ih (max acc x) ?_
    rcases h with hd | hm
    · exact Or.inl (hd.trans (le_max_left ..))
    · rcases List.mem_cons.mp hm with he | ht
      · subst x
        exact Or.inl (le_max_right ..)
      · exact Or.inr ht

private abbrev ScaledTerm := ℤ × ℕ × ℚ

private def scaledTerm (t : SplineTerm) : ScaledTerm :=
  (((grid : ℚ) * t.knot).num, t.degree, t.coefficient / (grid : ℚ) ^ t.degree)

private def packTerm (D : ℕ) (jets : List GridJet) : ScaledTerm → List GridJet :=
  fun (k, j, c) => if c = 0 then jets
    else addJet ⟨k, singleCoefficient j (c.num * (D / c.den : ℕ))⟩ jets

private theorem packedCoefficient_eq {D : ℕ} {c : ℚ} (hd : c.den ∣ D) :
    ((c.num * (D / c.den : ℕ) : ℤ) : ℚ) = (D : ℚ) * c := by
  have hn : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
  calc
    _ = (D : ℚ) * ((c.num : ℚ) / c.den) := by
      simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_div hd hn]
      ring
    _ = _ := by rw [Rat.num_div_den]

private theorem packTerm_weighted {D : ℕ} (jets : List GridJet) (t : ScaledTerm)
    (hd : t.2.2.den ∣ D) (f : ℤ → ℕ → ℚ) :
    weightedJets (packTerm D jets t) f =
      weightedJets jets f + (D : ℚ) * (t.2.2 * f t.1 t.2.1) := by
  rcases t with ⟨k, j, c⟩
  dsimp only [packTerm]
  by_cases hz : c = 0
  · simp [hz]
  · rw [if_neg hz, weightedJets_addJet, weightedJet_singleCoefficient, packedCoefficient_eq hd]
    ring

private theorem packedJets_weighted {D : ℕ} (terms : List ScaledTerm) (jets : List GridJet)
    (hd : ∀ t ∈ terms, t.2.2.den ∣ D) (f : ℤ → ℕ → ℚ) :
    weightedJets (terms.foldl (packTerm D) jets) f =
      weightedJets jets f + (D : ℚ) * (terms.map fun t => t.2.2 * f t.1 t.2.1).sum := by
  induction terms generalizing jets with
  | nil => simp
  | cons t terms ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih _ (fun u hu => hd u (List.mem_cons_of_mem t hu)), packTerm_weighted _ t (hd t List.mem_cons_self)]
    ring

private theorem packedJets_degree_bound {D d : ℕ} (terms : List ScaledTerm) (jets : List GridJet)
    (hd : ∀ t ∈ terms, t.2.1 ≤ d) (hj : ∀ q ∈ jets, q.coefficients.size ≤ d + 1) :
    ∀ q ∈ terms.foldl (packTerm D) jets, q.coefficients.size ≤ d + 1 := by
  induction terms generalizing jets with
  | nil => exact hj
  | cons t terms ih =>
    have htd := hd t List.mem_cons_self
    rcases t with ⟨k, j, c⟩
    apply ih _ (fun u hu => hd u (List.mem_cons_of_mem _ hu))
    dsimp only [packTerm]
    split_ifs
    · exact hj
    · refine addJet_degree_bound _ _ ?_ _ hj
      change (singleCoefficient j _).size ≤ d + 1
      rw [size_singleCoefficient]
      exact Nat.succ_le_succ htd

/-- A successful integer packing represents exactly the original rational coefficients. -/
theorem GridSpline.pack_sound {p : Spline} {q : GridSpline}
    (hq : GridSpline.pack p = some q) : q.Represents p := by
  let terms := p.map scaledTerm
  let D := terms.foldl (fun d t => d.lcm t.2.2.den) 1
  let degree := terms.foldl (fun d t => max d t.2.1) 0
  have hk : ∀ t ∈ p, ((grid : ℚ) * t.knot).den = 1 := by
    unfold GridSpline.pack at hq
    split at hq
    next h => contradiction
    next h =>
      have he : p.all (fun t => ((grid : ℚ) * t.knot).den == 1) = true := by
        cases hb : p.all (fun t => ((grid : ℚ) * t.knot).den == 1) <;> simp [hb] at h ⊢
      intro t ht
      simpa only [beq_iff_eq] using (List.all_eq_true.mp he) t ht
  have hQ : q = ⟨D, degree, terms.foldl (packTerm D) []⟩ := by
    unfold GridSpline.pack at hq
    have he : p.all (fun t => ((grid : ℚ) * t.knot).den == 1) = true :=
      List.all_eq_true.mpr fun t ht => beq_iff_eq.mpr (hk t ht)
    simpa only [he, Bool.not_true, Bool.false_eq_true, if_false, Option.some.injEq,
      D, degree, terms, scaledTerm, packTerm] using hq.symm
  have hD : 0 < D := foldl_lcm_pos _ terms (fun t _ => t.2.2.den_pos) Nat.one_pos
  have hd : ∀ t ∈ terms, t.2.2.den ∣ D := by
    intro t ht
    unfold D
    rw [← List.foldl_map]
    exact foldl_lcm_dvd _ _ _ (Or.inr (List.mem_map.mpr ⟨t, ht, rfl⟩))
  have hdeg : ∀ t ∈ terms, t.2.1 ≤ degree := by
    intro t ht
    unfold degree
    rw [← List.foldl_map]
    exact foldl_max_bound _ _ _ (Or.inr (List.mem_map.mpr ⟨t, ht, rfl⟩))
  rw [hQ]
  refine ⟨hD.ne', packedJets_degree_bound terms [] hdeg (by simp), fun f => ?_⟩
  simp only
  rw [packedJets_weighted terms [] hd]
  simp only [weightedJets, List.map_nil, List.sum_nil, zero_add]
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  rw [mul_div_cancel_left₀ _ hD']
  unfold terms weightedSpline
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  have hk' : (((grid : ℚ) * t.knot).num : ℚ) = (grid : ℚ) * t.knot := by
    have h := Rat.num_div_den ((grid : ℚ) * t.knot)
    simpa only [hk t ht, Nat.cast_one, div_one] using h
  simp only [scaledTerm, hk']
  have hg := ratGrid_ne_zero
  field_simp

private theorem cache_get {p : GridSpline} {bound n : ℕ} (hn : n ≤ bound) :
    (p.cache bound)[n]? = some (p.primitive n) := by
  simp only [GridSpline.cache, Array.getElem?_map, List.getElem?_toArray,
    List.getElem?_range (Nat.lt_succ_of_le hn), Option.map_some]

/-- The cached integer evaluator can replace the rational primitive evaluator at all
inputs. Points and orders outside its cache automatically use the latter. -/
theorem gridPrimitives_sound {q : GridSpline} {p : Spline} (hq : q.Represents p)
    (bound : ℕ) :
    gridPrimitives (q.cache bound) (splinePrimitives p) = splinePrimitives p := by
  funext n x
  unfold gridPrimitives
  by_cases hn : n ≤ bound
  · rw [cache_get hn]
    dsimp only
    split_ifs with hx <;> try rfl
    have he := Rat.num_div_den ((grid : ℚ) * x)
    rw [hx, Nat.cast_one, div_one] at he
    rw [q.primitive_eval_sound hq, he]
    congr 1
    exact mul_div_cancel_left₀ _ ratGrid_ne_zero
  · have hs : (q.cache bound).size ≤ n := by
      simp [GridSpline.cache]
      omega
    rw [Array.getElem?_eq_none hs]

private def arrayWeight (a : Array ℤ) (f : ℕ → ℚ) : ℚ :=
  ∑ i ∈ Finset.range a.size, (a[i]?.getD 0 : ℚ) * f i

private theorem arrayWeight_modify (a : Array ℤ) (f : ℕ → ℚ) {i : ℕ} (hi : i < a.size) (z : ℤ) :
    arrayWeight (a.modify i (· + z)) f = arrayWeight a f + (z : ℚ) * f i := by
  unfold arrayWeight
  rw [Array.size_modify]
  have hsum : (∑ j ∈ Finset.range a.size, if i = j then (z : ℚ) * f i else 0) =
      (z : ℚ) * f i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      exact if_neg (Ne.symm hj)
    · exact fun h => (h (Finset.mem_range.mpr hi)).elim
  rw [← hsum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Array.getElem?_modify]
  by_cases h : i = j
  · subst j
    rw [if_pos rfl, if_pos rfl, Array.getElem?_eq_getElem hi]
    simp only [Option.map_some, Option.getD_some, Int.cast_add]
    ring
  · simp [h]

private theorem weighted_foldl_of_step {α : Type*} (xs : List α) (step : Array ℤ → α → Array ℤ)
    (arr : Array ℤ) (f : ℕ → ℚ) (term : α → ℚ)
    (hstep : ∀ x ∈ xs, ∀ a : Array ℤ, a.size = arr.size →
      (step a x).size = arr.size ∧ arrayWeight (step a x) f = arrayWeight a f + term x) :
    (xs.foldl step arr).size = arr.size ∧
      arrayWeight (xs.foldl step arr) f = arrayWeight arr f + (xs.map term).sum := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
    have hs := hstep x List.mem_cons_self arr rfl
    have ht := ih (step arr x) (fun y hy a ha => by
      have q := hstep y (List.mem_cons_of_mem x hy) a (ha.trans hs.1)
      exact ⟨q.1.trans hs.1.symm, q.2⟩)
    refine ⟨ht.1.trans hs.1, ?_⟩
    rw [List.foldl_cons, ht.2, hs.2, List.map_cons, List.sum_cons, add_assoc]

private theorem convolveCoefficients_eq_foldl (a b : Array ℤ) :
    convolveCoefficients a b =
      (List.range a.size).foldl (fun arr i =>
        (List.range b.size).foldl (fun arr j =>
          arr.modify (i+j+1) (· + a[i]?.getD 0 * b[j]?.getD 0)) arr)
        (Array.replicate (a.size+b.size) 0) := by
  unfold convolveCoefficients
  simp [Std.Legacy.Range.size, ← List.range_eq_range']

private theorem sum_map_range (n : ℕ) (f : ℕ → ℚ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private theorem convolveCoefficients_inner (a b arr : Array ℤ) (f : ℕ → ℚ)
    (i : ℕ) (hi : i < a.size) (harr : arr.size = a.size+b.size) :
    let r := (List.range b.size).foldl (fun arr j =>
      arr.modify (i+j+1) (· + a[i]?.getD 0 * b[j]?.getD 0)) arr
    r.size = arr.size ∧ arrayWeight r f = arrayWeight arr f +
      ∑ j ∈ Finset.range b.size,
        (a[i]?.getD 0 : ℚ) * (b[j]?.getD 0 : ℚ) * f (i+j+1) := by
  have H := weighted_foldl_of_step (List.range b.size)
    (fun (arr : Array ℤ) j => arr.modify (i+j+1) (· + a[i]?.getD 0 * b[j]?.getD 0))
    arr f (fun j => (a[i]?.getD 0 : ℚ) * (b[j]?.getD 0 : ℚ) * f (i+j+1)) (by
      intro j hj u hu
      have hj' := List.mem_range.mp hj
      have hb : i+j+1 < u.size := by omega
      exact ⟨(Array.size_modify).trans hu, by
        rw [arrayWeight_modify u f hb]
        push_cast
        rfl⟩)
  rw [sum_map_range] at H
  exact H

private theorem convolveCoefficients_weighted (a b : Array ℤ) (f : ℕ → ℚ) :
    (convolveCoefficients a b).size = a.size + b.size ∧
      arrayWeight (convolveCoefficients a b) f =
        ∑ i ∈ Finset.range a.size, ∑ j ∈ Finset.range b.size,
          (a[i]?.getD 0 : ℚ) * (b[j]?.getD 0 : ℚ) * f (i+j+1) := by
  let init : Array ℤ := Array.replicate (a.size+b.size) 0
  have hs : init.size = a.size + b.size := Array.size_replicate
  have hv : arrayWeight init f = 0 := by
    unfold arrayWeight
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp [init, show i < a.size + b.size by omega]
  have H := weighted_foldl_of_step (List.range a.size)
    (fun (arr : Array ℤ) i =>
      (List.range b.size).foldl (fun arr j =>
        arr.modify (i+j+1) (· + a[i]?.getD 0 * b[j]?.getD 0)) arr)
    init f (fun i => ∑ j ∈ Finset.range b.size,
      (a[i]?.getD 0 : ℚ) * (b[j]?.getD 0 : ℚ) * f (i+j+1)) (by
        intro i hi u hu
        have h := convolveCoefficients_inner a b u f i (List.mem_range.mp hi) (hu.trans hs)
        exact ⟨h.1.trans hu, h.2⟩)
  rw [sum_map_range, hv, zero_add, hs] at H
  rw [convolveCoefficients_eq_foldl]
  exact H

private def convolveJets (a b : GridJet) : GridJet :=
  ⟨a.knot+b.knot, convolveCoefficients a.coefficients b.coefficients⟩

private theorem convolveJets_weighted (a b : GridJet) (f : ℤ → ℕ → ℚ) :
    (convolveJets a b).weighted f =
      a.weighted (fun k i => b.weighted (fun l j => f (k+l) (i+j+1))) := by
  change arrayWeight (convolveCoefficients a.coefficients b.coefficients) (f (a.knot+b.knot)) = _
  rw [(convolveCoefficients_weighted _ _ _).2]
  simp only [GridJet.weighted]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem weightedJets_foldl_addJet {α : Type*} (mk : α → GridJet) (xs : List α)
    (acc : List GridJet) (f : ℤ → ℕ → ℚ) :
    weightedJets (xs.foldl (fun ys x => addJet (mk x) ys) acc) f =
      weightedJets acc f + (xs.map (fun x => (mk x).weighted f)).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, weightedJets_addJet]
    simp only [List.map_cons, List.sum_cons]
    ac_rfl

private theorem degree_foldl_addJet {α : Type*} (mk : α → GridJet) (xs : List α)
    (acc : List GridJet) (d : ℕ) (hm : ∀ x ∈ xs, (mk x).coefficients.size ≤ d)
    (ha : ∀ a ∈ acc, a.coefficients.size ≤ d) :
    ∀ t ∈ xs.foldl (fun ys x => addJet (mk x) ys) acc, t.coefficients.size ≤ d := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons x xs ih =>
    exact ih _ (fun y hy => hm y (List.mem_cons_of_mem x hy))
      (addJet_degree_bound d (mk x) (hm x List.mem_cons_self) acc ha)

private theorem weightedJet_add (a : GridJet) (f g : ℤ → ℕ → ℚ) :
    a.weighted (fun k j => f k j + g k j) = a.weighted f + a.weighted g := by
  simp only [GridJet.weighted, mul_add, Finset.sum_add_distrib]

private theorem weightedJet_convolve_list (a : GridJet) (q : List GridJet) (f : ℤ → ℕ → ℚ) :
    (q.map (fun b => (convolveJets a b).weighted f)).sum =
      a.weighted (fun k i => weightedJets q (fun l j => f (k+l) (i+j+1))) := by
  induction q with
  | nil => simp [weightedJets, GridJet.weighted]
  | cons b bs ih =>
    change (convolveJets a b).weighted f + (bs.map (fun b => (convolveJets a b).weighted f)).sum =
      a.weighted (fun k i => b.weighted (fun l j => f (k+l) (i+j+1)) +
        weightedJets bs (fun l j => f (k+l) (i+j+1)))
    rw [convolveJets_weighted, ih, weightedJet_add]

private theorem weightedJets_foldl_convolve (p q acc : List GridJet) (f : ℤ → ℕ → ℚ) :
    weightedJets (p.foldl (fun acc a => q.foldl (fun zs b => addJet (convolveJets a b) zs) acc)
      acc) f =
      weightedJets acc f + weightedJets p (fun k i => weightedJets q (fun l j => f (k+l) (i+j+1))) := by
  induction p generalizing acc with
  | nil => simp [weightedJets]
  | cons a p ih =>
    rw [List.foldl_cons, ih, weightedJets_foldl_addJet (convolveJets a)]
    rw [weightedJet_convolve_list]
    simp only [weightedJets, List.map_cons, List.sum_cons, add_assoc]

private theorem convolveJets_degree_bound (P Q : GridSpline)
    (hp : ∀ a ∈ P.jets, a.coefficients.size ≤ P.degree + 1)
    (hq : ∀ b ∈ Q.jets, b.coefficients.size ≤ Q.degree + 1) :
    ∀ jet ∈ (P.convolution Q).jets, jet.coefficients.size ≤ (P.convolution Q).degree + 1 := by
  unfold GridSpline.convolution
  simp only
  generalize he : P.jets = p at *
  have hb (a : GridJet) (ha : a.coefficients.size ≤ P.degree + 1) (b : GridJet) (hb : b ∈ Q.jets) :
      (convolveJets a b).coefficients.size ≤ P.degree + Q.degree + 1 + 1 := by
    change (convolveCoefficients a.coefficients b.coefficients).size ≤ _
    rw [(convolveCoefficients_weighted _ _ (fun _ => 0)).1]
    have hb' := hq b hb
    omega
  have hi (acc : List GridJet) (hacc : ∀ z ∈ acc, z.coefficients.size ≤ P.degree + Q.degree + 1 + 1) :
      ∀ jet ∈ p.foldl (fun acc a => Q.jets.foldl (fun acc b => addJet (convolveJets a b) acc) acc) acc,
        jet.coefficients.size ≤ P.degree + Q.degree + 1 + 1 := by
    clear he
    induction p generalizing acc with
    | nil => exact hacc
    | cons a p ih =>
      exact ih (fun b hb => hp b (List.mem_cons_of_mem a hb)) _
        (degree_foldl_addJet (convolveJets a) Q.jets acc _
          (hb a (hp a List.mem_cons_self)) hacc)
  exact hi [] (by simp)

private theorem weightedSpline_convolution (p q : Spline) (f : ℚ → ℕ → ℚ) :
    weightedSpline (p.convolution q) f =
      weightedSpline p (fun k i => weightedSpline q (fun l j => f (k+l) (i+j+1))) := by
  induction p with
  | nil => simp [weightedSpline, Spline.convolution]
  | cons t p ih =>
    simp only [weightedSpline, Spline.convolution, List.flatMap_cons, List.map_append,
      List.sum_append, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, ← List.sum_map_mul_left]
    apply congrArg (fun x : ℚ => x + _)
    simp only [List.map_map, Function.comp_def, mul_assoc]

private theorem weightedJets_convolution (P Q : GridSpline) (f : ℤ → ℕ → ℚ) :
    weightedJets (P.convolution Q).jets f =
      weightedJets P.jets (fun k i => weightedJets Q.jets (fun l j => f (k+l) (i+j+1))) := by
  have h := weightedJets_foldl_convolve P.jets Q.jets [] f
  simpa only [GridSpline.convolution, convolveJets, weightedJets, List.map_nil, List.sum_nil,
    zero_add] using h

private theorem weightedJets_conv_rescale {Q : GridSpline} {q : Spline}
    (hQ : Q.Represents q) (f : ℚ → ℕ → ℚ) (k : ℤ) (i : ℕ) :
    weightedJets Q.jets (fun l j =>
      (grid : ℚ) ^ (i+j+1) * f (((k+l : ℤ) : ℚ) / grid) (i+j+1)) =
      ((grid : ℚ) * (Q.denominator : ℚ)) * ((grid : ℚ)^i *
        weightedSpline q (fun l j => f ((k : ℚ)/grid + l) (i+j+1))) := by
  let W := fun l j => f ((k : ℚ)/grid + l) (i+j+1)
  have hf : (fun (l : ℤ) (j : ℕ) => (grid : ℚ) ^ (i+j+1) *
      f (((k+l : ℤ) : ℚ) / grid) (i+j+1)) =
      fun (l : ℤ) (j : ℕ) => ((grid : ℚ) * (grid : ℚ)^i) * ((grid : ℚ)^j * W ((l : ℚ)/grid) j) := by
    funext l j
    rw [pow_succ, pow_add, Int.cast_add, add_div]
    unfold W
    ring
  rw [hf, weightedJets_mul]
  change _ = _ * (_ * weightedSpline q W)
  rw [hQ.2.2 W]
  have hden : (Q.denominator : ℚ) ≠ 0 := by exact_mod_cast hQ.1
  field_simp

/-- The integer convolution implements the rational truncated-power convolution exactly. -/
theorem GridSpline.convolution_sound {P Q : GridSpline} {p q : Spline}
    (hp : P.Represents p) (hq : Q.Represents q) : (P.convolution Q).Represents (p.convolution q) := by
  refine ⟨Nat.mul_ne_zero (Nat.mul_ne_zero hp.1 hq.1) (by decide), convolveJets_degree_bound P Q hp.2.1 hq.2.1,
    fun f => ?_⟩
  rw [weightedSpline_convolution, hp.2.2, weightedJets_convolution]
  simp_rw [weightedJets_conv_rescale hq]
  rw [weightedJets_mul]
  change _ = _ / ((P.denominator * Q.denominator * grid : ℕ) : ℚ)
  push_cast
  have hP : (P.denominator : ℚ) ≠ 0 := by exact_mod_cast hp.1
  have hQ : (Q.denominator : ℚ) ≠ 0 := by exact_mod_cast hq.1
  have hG := ratGrid_ne_zero
  field_simp

/-- A row's cached jet data, whenever present, represents the row's rational spline. -/
def GridRow.PackedSound (r : GridRow) : Prop :=
  ∀ p, r.packed = some p → p.Represents r.row.profile

theorem prepareGrid_packedSound (r : Rows.RowData) : (prepareGrid r).PackedSound :=
  fun _ hp => GridSpline.pack_sound hp

theorem GridRow.packedSound_setWeight {r : GridRow} (hr : r.PackedSound) (w : ℚ) :
    ({ r with row := { r.row with weight := w } } : GridRow).PackedSound :=
  hr

/-- Valid cached rows produce the same Gram entry as the exact rational path. -/
theorem gramGrid_sound_of_pack {l r : GridRow} (hl : l.PackedSound) (hr : r.PackedSound) :
    gramGrid l r = gram l.row r.row := by
  unfold gramGrid
  dsimp only
  cases hP : l.packed with
  | none => rfl
  | some P =>
    cases hQ : r.packed with
    | none => rfl
    | some Q =>
      dsimp only
      rw [gridPrimitives_sound (GridSpline.convolution_sound (hl P hP) (hr Q hQ))]
      rfl

theorem gramGrid_sound (p q : Rows.RowData) :
    gramGrid (prepareGrid p) (prepareGrid q) = gram (prepare p) (prepare q) :=
  gramGrid_sound_of_pack (prepareGrid_packedSound p) (prepareGrid_packedSound q)

/-- A valid cached Taylor profile and row give the same rational central interval
as the exact truncated-power implementation. -/
theorem centralGrid_sound_of_pack {center : Option GridSpline} {r : GridRow}
    (hc : ∀ p, center = some p → p.Represents hstarSpline) (hr : r.PackedSound) :
    centralGrid center r = central r.row := by
  unfold centralGrid
  dsimp only
  split_ifs with h
  · simp [central, centralFromSpline, h]
  · cases hP : center with
    | none => rfl
    | some P =>
      cases hQ : r.packed with
      | none => rfl
      | some Q =>
        dsimp only
        rw [gridPrimitives_sound (GridSpline.convolution_sound (hc P hP) (hr Q hQ))]
        simp [central, centralFromSpline, h]

theorem centralGrid_sound (r : Rows.RowData) :
    centralGrid (GridSpline.pack hstarSpline) (prepareGrid r) = central (prepare r) :=
  centralGrid_sound_of_pack (fun _ h => GridSpline.pack_sound h) (prepareGrid_packedSound r)

end Chowla.Checker

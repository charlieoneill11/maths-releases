import Chowla.Model.Moments
import Chowla.VariationalFourier
import Chowla.VariationalWeighted

namespace Chowla

open Filter MeasureTheory MvPolynomial
open scoped BigOperators FourierTransform SchwartzMap Topology

theorem MomentTest.profile_isProfile (f : MomentTest) : IsProfile f.profile := by
  let fC := f.toSchwartz.postcompCLM Complex.ofRealCLM
  have hc : Continuous f.profile :=
    Complex.continuous_re.comp (𝓕 fC).continuous
  have hk : HasCompactSupport f.profile :=
    f.compactFourier.comp_left Complex.zero_re
  have he : Function.Even f.profile := by
    intro x
    let g := fun u : ℝ => (f.toSchwartz u : ℂ)
    have hcomp : g ∘ LinearIsometryEquiv.neg ℝ (E := ℝ) = g := by
      funext u
      change (f.toSchwartz (-u) : ℂ) = (f.toSchwartz u : ℂ)
      exact congrArg (fun a : ℝ => (a : ℂ)) (f.even u)
    have h := Real.fourier_comp_linearIsometry
      (LinearIsometryEquiv.neg ℝ (E := ℝ)) g x
    rw [hcomp] at h
    exact congrArg Complex.re h.symm
  exact ⟨hc.measurable, he, (hk.isCompact_range hc).isBounded, hk⟩

/-- A word in linear statistics, represented by its list of Schwartz tests. -/
noncomputable def MomentWord.statistic (L : List MomentTest) (X : ℝ) (d : ℤ) : ℝ :=
  (L.map fun f => zeroStatistic (fun x => f.toSchwartz x) d X).prod

noncomputable def MomentWord.model (L : List MomentTest) : Model :=
  (L.map fun f => stat f.profile).prod

noncomputable def MomentWord.bandwidth (L : List MomentTest) : ℝ :=
  (L.map fun f => radius f.profile).sum

private theorem MomentWord.modelExpectation_eq (L : List MomentTest) :
    modelExpectation (MomentWord.model L) = modelMoment (fun i : Fin L.length => (L.get i).profile) := by
  change modelExpectation (List.map (stat ∘ MomentTest.profile) L).prod = _
  rw [← List.map_map]
  have h : ∀ h ∈ L.map MomentTest.profile, IsProfile h := by
    intro h hm
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hm
    exact f.profile_isProfile
  rw [modelExpectation_monomial_of_isProfile _ h]
  unfold listMoment
  have hcast {n n' : ℕ} (hn : n = n') (f : Fin n → FourierProfile) :
      modelMoment f = modelMoment (fun i : Fin n' => f (Fin.cast hn.symm i)) := by
    subst n'
    rfl
  rw [hcast (List.length_map MomentTest.profile)]
  congr 1
  funext i
  simp [List.get_eq_getElem]

/-- Specialising Theorem 7 to the product associated with a nonempty word. -/
theorem momentWord_limit (m : PaperClaims) (D : DiscClass) (W : ShellWeight) (L : List MomentTest)
    (hL : L ≠ []) (hr : MomentWord.bandwidth L < 2) :
    Tendsto (fun X => weightedAverage D W X (MomentWord.statistic L X)) atTop
      (𝓝 (modelExpectation (MomentWord.model L))) := by
  have hlen : 0 < L.length := by cases L <;> simp_all
  have hsum : ∑ i : Fin L.length, radius ((L.get i).profile) = MomentWord.bandwidth L := by
    rw [← List.sum_ofFn]
    change (List.ofFn (fun i : Fin L.length => radius (L[(i : Nat)]).profile)).sum = _
    exact congrArg List.sum (List.ofFn_getElem_eq_map L (fun f => radius f.profile))
  have hprod (X : ℝ) (d : ℤ) :
      ∏ i : Fin L.length, zeroStatistic (fun x => (L.get i).toSchwartz x) d X =
        MomentWord.statistic L X d := by
    rw [← List.prod_ofFn]
    change (List.ofFn (fun i : Fin L.length => zeroStatistic (fun x => L[(i : Nat)].toSchwartz x) d X)).prod = _
    exact congrArg List.prod (List.ofFn_getElem_eq_map L
      (fun f => zeroStatistic (fun x => f.toSchwartz x) d X))
  simpa only [← MomentWord.modelExpectation_eq, hprod] using
    m.emptyPatternMoments D W L.length hlen L.get (by rwa [hsum])

theorem weightedAverage_add (D : DiscClass) (W : ShellWeight) (X : ℝ) (f g : ℤ → ℝ) :
    weightedAverage D W X (f + g) = weightedAverage D W X f + weightedAverage D W X g := by
  simp [weightedAverage, weightedSum, mul_add, Finset.sum_add_distrib, add_div]

theorem weightedAverage_const_mul (D : DiscClass) (W : ShellWeight) (X c : ℝ) (f : ℤ → ℝ) :
    weightedAverage D W X (fun d => c * f d) = c * weightedAverage D W X f := by
  have ht (d : ℤ) : W.toFun (oddPart D d / X) * (c * f d) =
      c * (W.toFun (oddPart D d / X) * f d) := by ring
  simp [weightedAverage, weightedSum, ht, ← Finset.mul_sum, mul_div_assoc]

/-- A finite polynomial written as coefficients times words in linear statistics. -/
abbrev MomentPolynomial := List (ℝ × List MomentTest)

noncomputable def MomentPolynomial.statistic (P : MomentPolynomial) (X : ℝ) (d : ℤ) : ℝ :=
  (P.map fun t => t.1 * MomentWord.statistic t.2 X d).sum

noncomputable def MomentPolynomial.model (P : MomentPolynomial) : Model :=
  (P.map fun t => C t.1 * MomentWord.model t.2).sum

/-- Theorem 7 on a finite sum of supported nonempty monomials. -/
theorem momentPolynomial_limit (m : PaperClaims) (D : DiscClass) (W : ShellWeight)
    (P : MomentPolynomial)
    (hP : ∀ t ∈ P, t.2 ≠ [] ∧ MomentWord.bandwidth t.2 < 2) :
    Tendsto (fun X => weightedAverage D W X (MomentPolynomial.statistic P X)) atTop
      (𝓝 (modelExpectation (MomentPolynomial.model P))) := by
  induction P with
  | nil =>
      simp [MomentPolynomial.statistic, MomentPolynomial.model, weightedAverage, weightedSum,
        modelExpectation]
  | cons t ts ih =>
      have ht := hP t (List.mem_cons_self ..)
      have hs := ih (fun s hs => hP s (List.mem_cons_of_mem _ hs))
      have hm := (momentWord_limit m D W t.2 ht.1 ht.2).const_mul t.1
      have hw (X : ℝ) : MomentPolynomial.statistic (t :: ts) X =
          (fun d => t.1 * MomentWord.statistic t.2 X d) + MomentPolynomial.statistic ts X := by
        rfl
      have hE : modelExpectation (MomentPolynomial.model (t :: ts)) =
          t.1 * modelExpectation (MomentWord.model t.2) +
            modelExpectation (MomentPolynomial.model ts) := by
        simp only [modelExpectation_eq_linear, MomentPolynomial.model, List.map_cons, List.sum_cons, map_add]
        rw [show C t.1 * MomentWord.model t.2 = t.1 • MomentWord.model t.2 from
          (Algebra.smul_def t.1 _).symm, map_smul, smul_eq_mul]
      simpa only [hw, weightedAverage_add, weightedAverage_const_mul, hE] using hm.add hs

end Chowla

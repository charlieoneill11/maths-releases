import HadwigerNelson.Stars.Partial.Cache
import HadwigerNelson.Stars.Partial.Spans
import HadwigerNelson.Stars.MomentSums
import HadwigerNelson.Arithmetic.Magnitude
import Mathlib.Analysis.Complex.Basic

namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (Span exactPhase phaseTriple exactTerm spanEval)
open Arithmetic GaussianInt
noncomputable section

/-- Each fixed-point power uses the same 6k coordinate-unit allowance as in §3.2. -/
theorem power_error (q i : Nat) (k : Fin frequencyCount) :
    ‖GaussianInt.value scale ((powerEntry q i)[k.val]?.getD default) - exactPhase q i^(k.val+1)‖ ≤
      6*(k.val+1:Nat)/(scale:ℝ) := by
  obtain ⟨hd,hu⟩ := BoxCheck.phaseTriple_spec q i
  have bound : k.val<309 := k.isLt
  have sm : 6*(k.val+1)≤1854 := by omega
  have wide : 6*((k.val+1:Nat):ℝ) ≤ (scale:ℝ) := calc
    _ ≤ (1854:ℝ) := by exact_mod_cast sm
    _ ≤ _ := by norm_num [scale]
  simpa only [powerEntry,GaussianInt.powerTable_get _ _ _ _ k.isLt,Option.getD_some,Nat.cast_mul,Nat.cast_ofNat] using
    GaussianInt.rational_power_error scale _ _ _ (k.val+1) (by decide) hd hu wide

theorem one_term (p : Span) (valid : ValidSpan p) (k : Fin frequencyCount) :
    ‖GaussianInt.value scale ((uncached p).term k.val)-exactTerm p (k.val+1)‖ ≤
      12*(k.val+1:Nat)/(scale:ℝ) := by
  let A := ((powerEntry p.quadrant p.start)[k.val]?).getD default
  let B := ((powerEntry p.quadrant p.stop)[k.val]?).getD default
  have eq : GaussianInt.value scale ((uncached p).term k.val) =
      (p.coeff:ℂ)*(GaussianInt.value scale A - GaussianInt.value scale B) := by
    apply Complex.ext <;> simp [uncached,PairMoments.term,GaussianInt.value,A,B] <;> ring
  rw [eq,exactTerm,←mul_sub,Complex.norm_mul]
  have unit : ‖(p.coeff:ℂ)‖=1 := by
    rw [Complex.norm_intCast]
    rcases valid.2.2.2 with h|h <;> rw [h] <;> norm_num
  rw [unit,one_mul]
  have both := norm_sub_le
    (GaussianInt.value scale A-exactPhase p.quadrant p.start^(k.val+1))
    (GaussianInt.value scale B-exactPhase p.quadrant p.stop^(k.val+1))
  have bound := both.trans (add_le_add (power_error p.quadrant p.start k) (power_error p.quadrant p.stop k))
  calc
    _ = ‖(GaussianInt.value scale A-exactPhase p.quadrant p.start^(k.val+1))-
        (GaussianInt.value scale B-exactPhase p.quadrant p.stop^(k.val+1))‖ := by congr 1;abel
    _ ≤ _ := bound
    _ = _ := by ring

theorem sumTerms_components (terms : Array PairMoments) (k : Nat) :
    (sumTerms terms k).re=∑ i : Fin terms.size, (terms[i.val].term k).re ∧
    (sumTerms terms k).im=∑ i : Fin terms.size, (terms[i.val].term k).im := by
  let add (p : GaussianInt) (t : PairMoments) : GaussianInt :=
    ⟨p.re+(t.term k).re,p.im+(t.term k).im⟩
  have loop (xs : List PairMoments) (p : GaussianInt) :
      (xs.foldl add p).re=p.re+(xs.map (fun t => (t.term k).re)).sum ∧
      (xs.foldl add p).im=p.im+(xs.map (fun t => (t.term k).im)).sum := by
    induction xs generalizing p with
    | nil => simp
    | cons t xs ih =>
      simpa [add,add_assoc] using ih (add p t)
  have h := loop terms.toList ⟨0,0⟩
  simp only [←Array.foldl_toList,sumTerms]
  have fin (f : PairMoments → Int) :
      (terms.toList.map f).sum=∑ i : Fin terms.size, f terms[i.val] := by
    conv_lhs => rw [←List.ofFn_getElem (xs:=terms.toList)]
    simp [List.map_ofFn,List.sum_ofFn]
  simpa only [zero_add,fin] using h

theorem sum_error (src : Angular.Box) (other : Nat) (k : Fin frequencyCount) :
    let ss := runs src other
    let z := sumTerms (ss.map uncached) k.val
    ‖GaussianInt.value scale z - spanEval ss (fun p => exactTerm p (k.val+1))‖ ≤
      ss.size*(12*(k.val+1:Nat)/(scale:ℝ)) := by
  let ss := runs src other
  let z := sumTerms (ss.map uncached) k.val
  have sum := sumTerms_components (ss.map uncached) k.val
  have eq : GaussianInt.value scale z =
      ∑ i : Fin ss.size, GaussianInt.value scale ((uncached ss[i.val]).term k.val) := by
    apply Complex.ext <;>
      simp only [GaussianInt.value,z,sum.1,sum.2,Array.size_map,Array.getElem_map,Int.cast_sum,
        Complex.re_sum,Complex.im_sum,div_eq_mul_inv,Finset.sum_mul]
    all_goals
      apply Fintype.sum_equiv (finCongr (Array.size_map ..))
      intro i
      rfl
  change ‖GaussianInt.value scale z - spanEval ss _‖ ≤ _
  rw [eq,BoxCheck.spanEval_fin,←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ : Fin ss.size, (12*(k.val+1:Nat)/(scale:ℝ)) :=
      Finset.sum_le_sum (fun (i : Fin ss.size) _ =>
        one_term (ss[i.val]) (runs_valid src other _ (Array.getElem_mem i.isLt)) k)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; rfl

end
end HadwigerNelson.Stars.PartialCheck

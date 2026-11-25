import HadwigerNelson.Stars.PhaseMoments
import HadwigerNelson.Stars.CreditSound
import HadwigerNelson.Stars.Partition
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.BigOperators

/-! The exact error accumulated by the executable sums of signed harmonic
endpoints. The proof includes every frequency and both coordinates. -/

namespace HadwigerNelson.Stars.BoxCheck
open Arithmetic
open scoped BigOperators

theorem spanEval_fin {A : Type*} [AddCommGroup A] (s : Array Span) (f : Span → A) :
    spanEval s f = ∑ i : Fin s.size, f s[i.val] := by
  unfold spanEval
  conv_lhs => rw [← List.ofFn_getElem (xs := s.toList)]
  simp [List.map_ofFn,List.sum_ofFn]

theorem spanSum_eq (tab : Array Arc) (s : Array Span) (f : SpanMoments → Int) :
    spanSum (s.map (prepareSpan tab)) f = spanEval s (fun p => f (prepareSpan tab p)) := by
  have fold (xs : List Span) (z : Int) :
      xs.foldl (fun a p => a+f (prepareSpan tab p)) z =
        z+(xs.map (fun p => f (prepareSpan tab p))).sum := by
    induction xs generalizing z with
    | nil => simp
    | cons p xs ih => simp [ih,add_assoc]
  rw [spanSum,←Array.foldl_toList,Array.toList_map,List.foldl_map,fold,zero_add]
  rfl

theorem spanEval_cast (s : Array Span) (f : Span → Int) :
    ((spanEval s f : Int) : ℝ) = spanEval s (fun p => (f p : ℝ)) := by
  simp only [spanEval_fin,Int.cast_sum]

noncomputable def exactTerm (s : Span) (k : Nat) : ℂ :=
  (s.coeff : ℂ)*(exactPhase s.quadrant s.start^k-exactPhase s.quadrant s.stop^k)

theorem exactTerm_eq (s : Span) (k : Nat) :
    exactTerm s k = changeOf (fun q c _ i => -(c : ℂ)*exactPhase q i^k) s := by
  unfold exactTerm changeOf
  ring

theorem sum_terms_error (table : Array Arc) (spans : Array Span) (k : Fin harmonics) :
    let terms := spans.map (prepareSpan table)
    let x := spanSum terms (fun m => (m.term k.val).re)
    let y := spanSum terms (fun m => (m.term k.val).im)
    let mass := spanSum terms SpanMoments.mass
    ‖GaussianInt.value phaseScale ⟨x,y⟩-spanEval spans (fun p => exactTerm p (k.val+1))‖ ≤
      (mass : ℝ)*(12*(k.val+1 : Nat)/(phaseScale : ℝ)) := by
  dsimp only
  let w (s : Span) := (prepareSpan table s).term k.val
  have eq : GaussianInt.value phaseScale
      ⟨spanSum (spans.map (prepareSpan table)) (fun m => (m.term k.val).re),
       spanSum (spans.map (prepareSpan table)) (fun m => (m.term k.val).im)⟩ =
      ∑ i : Fin spans.size, GaussianInt.value phaseScale (w spans[i.val]) := by
    apply Complex.ext <;>
      simp only [GaussianInt.value,spanSum_eq,spanEval_fin,Int.cast_sum,Complex.re_sum,Complex.im_sum,
        div_eq_mul_inv,Finset.sum_mul,w]
  rw [eq,spanEval_fin,←Finset.sum_sub_distrib,spanSum_eq,spanEval_fin,Int.cast_sum,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  exact span_term_error table spans[i.val] k

end HadwigerNelson.Stars.BoxCheck

import HadwigerNelson.Stars.Partial.Layout
import HadwigerNelson.Stars.Partial.Moments
import HadwigerNelson.Stars.CellScore
import HadwigerNelson.Stars.RealFourier

namespace HadwigerNelson.Stars.PartialCheck
open BoxCheck (quant physicalSource)
open MeasureTheory
noncomputable section

/-- Signed row computed with an empty power cache. A verified nonempty cache
gives the same row by `row_cache`. -/
def sourceRow (i : Nat) : Row := (row arcTable (source i) {}).2

def powerFraction {d : Nat} (φ : Fin d → ℝ) (k : Nat) : ℝ :=
  ‖∑ j, anglePhase (φ j)^(k+1)‖ / d

def harmonicLocal {d : Nat} (k : Fin frequencyCount) (φ : Fin d → ℝ) (i : Fin 132621) : ℝ :=
  let r := sourceRow i.val
  max 0 ((r.mean : ℝ)/quant + ((r.spectrum[k.val]?.getD 0 : Int) : ℝ)/quant*powerFraction φ k.val)

def nativeLocal (d : Nat) (j : Fin 4122) : ℝ :=
  max 0 ((d : ℝ)*((sourceRow (132621+j.val)).mean : ℝ)/quant-1)

private abbrev Rect := Fin 132621 ⊕ Fin 4122

private def index : Rect → Fin 136743
  | .inl i => ⟨i.val,by omega⟩
  | .inr j => ⟨132621+j.val,by omega⟩

private theorem index_injective : Function.Injective index := by
  rintro (i|i) (j|j) eq
  all_goals have hx := congrArg Fin.val eq
  all_goals simp only [index] at hx
  · exact congrArg Sum.inl (Fin.ext hx)
  · omega
  · omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

private def localValue {d : Nat} (k : Fin frequencyCount) (φ : Fin d → ℝ) : Rect → ℝ
  | .inl i => harmonicLocal k φ i
  | .inr j => 2*nativeLocal d j/d

private theorem weight (L : Layout.Physical) (r : Rect) :
    volume.real (physicalSource (source (index r).val))/(PartialWave.datum.x*Wave.H) =
      2*((sourceRow (index r).val).area : ℝ)/PartialWave.xInt := by
  obtain ⟨x,y⟩ := L.widths (index r)
  rw [BoxCheck.physicalSource_area _ x.le y.le,PartialWave.datum_x]
  change ((source _).area : ℝ)/10^12 / (_*Wave.H) = 2*((source _).area : ℝ)/PartialWave.xInt
  norm_num [Wave.H,PartialWave.xInt]
  ring

attribute [local irreducible] sourceRow

private theorem pospart_div (a : ℝ) :
    max 0 (a/(quant : ℝ)) = max 0 a/(quant : ℝ) := by
  have Q : (0:ℝ)<quant := by norm_num [quant]
  by_cases h : 0 ≤ a
  · rw [max_eq_right h,max_eq_right (div_nonneg h Q.le)]
  · rw [max_eq_left (le_of_not_ge h),max_eq_left (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) Q.le),zero_div]

/-- Summing the local Fourier and native-only bounds over all 136,743
rectangles and their twelve disjoint images in a period cell gives this
normalized degree credit. The terms are expressed in the checker’s integer
units so the bucket computation can use the same row sums. -/
theorem summed_cell_bound (L : Layout.Physical) {d : Nat} (hd : 0<d)
    (k : Fin frequencyCount) (φ : Fin d → ℝ)
    (harmonic : ∀ (ψ : Fin d → ℝ) (i : Fin 132621) z, z ∈ physicalSource (source i.val) →
      (d:ℝ)/2*harmonicLocal k ψ i ≤ angularGain PartialWave.datum ψ z)
    (native : ∀ (ψ : Fin d → ℝ) (j : Fin 4122) z, z ∈ physicalSource (source (132621+j.val)) →
      nativeLocal d j ≤ angularGain PartialWave.datum ψ z) :
    2/((PartialWave.xInt : ℝ)*quant) * (∑ i : Fin 132621,
      ((sourceRow i.val).area:ℝ) * max 0 (((sourceRow i.val).mean:ℝ) +
          (((sourceRow i.val).spectrum[k.val]?.getD 0 : Int):ℝ)*powerFraction φ k.val)) +
      4/((PartialWave.xInt:ℝ)*quant*d) * (∑ j : Fin 4122,
        ((sourceRow (132621+j.val)).area:ℝ) * max 0 (((sourceRow (132621+j.val)).mean:ℝ)*d-quant))
      ≤ cellScore PartialWave.datum φ := by
  classical
  have D : (0:ℝ)<d := by exact_mod_cast hd
  have Q : (0:ℝ)<quant := by norm_num [quant]
  have realBound := normalized_cell_box_sum PartialWave.datum hd φ Finset.univ
    (fun r : Rect => physicalSource (source (index r).val)) (localValue k)
    (fun _ _ => (BoxCheck.physicalSource_open _).measurableSet)
    (fun e _ => L.subset (index e))
    (fun i _ j _ _ a b => by
      apply index_injective
      by_contra h
      exact Set.disjoint_left.mp (L.disjoint h) a b)
    (fun e _ b h => by
      cases e with
      | inl i => simp only [localValue,harmonicLocal,powerFraction,norm_anglePhase_signAngle]
      | inr j => rfl)
    (fun ψ e _ z hz => by
      cases e with
      | inl i => exact harmonic ψ i z hz
      | inr j =>
        change (d:ℝ)/2*(2*nativeLocal d j/d) ≤ _
        rw [show (d:ℝ)/2*(2*nativeLocal d j/d) = nativeLocal d j by field_simp]
        exact native ψ j z hz)
  simp_rw [weight L] at realBound
  rw [Fintype.sum_sum_type] at realBound
  refine le_trans (le_of_eq ?_) realBound
  rw [Finset.mul_sum,Finset.mul_sum]
  apply congrArg₂ HAdd.hAdd
  · apply Finset.sum_congr rfl
    intro i _
    simp only [index,localValue,harmonicLocal]
    set m := ((sourceRow i.val).mean : ℝ)
    set h := (((sourceRow i.val).spectrum[k.val]?.getD 0 : Int) : ℝ)
    set t := powerFraction φ k.val
    rw [show m/quant+h/quant*t = (m+h*t)/quant by ring,pospart_div]
    ring
  · apply Finset.sum_congr rfl
    intro j _
    simp only [index,localValue,nativeLocal]
    set m := ((sourceRow (132621+j.val)).mean : ℝ)
    rw [show (d:ℝ)*m/quant-1 = (m*d-quant)/quant by field_simp,pospart_div]
    ring

end
end HadwigerNelson.Stars.PartialCheck

import HadwigerNelson.Packing.AngularGap
import HadwigerNelson.Packing.Corners
import HadwigerNelson.Packing.Cosine
import Mathlib.Analysis.Real.Pi.Bounds

namespace HadwigerNelson.Packing
open Finset Crossings
noncomputable section

/-- A lower bound for the cosine of the angular gap and a uniform upper bound on the
squared normalized radial distance limit the number of separated points in any annulus. -/
theorem radial_card (P : Finset Plane) (z : Plane) {d l u C : ℝ} {k : ℕ}
    (hd : 0 < d) (sep : separated P d) (hk : 1 ≤ k)
    (radii : ∀ x ∈ P, dist x z/d ∈ Set.Icc l u)
    (cosBound : C ≤ Real.cos (2*Real.pi/(k+1 : ℝ)))
    (corner : ∀ a ∈ Set.Icc l u, ∀ b ∈ Set.Icc l u, a^2+b^2-2*a*b*C ≤ 1) :
    P.card ≤ k := by
  by_contra! big
  obtain ⟨x,hx,y,hy,ne,g,h0,hs,hg⟩ := angular_gap P z (by omega)
  have kpos : (0:ℝ)<(k:ℝ)+1 := by positivity
  have grow : (k:ℝ)+1 ≤ P.card := by exact_mod_cast big
  have gs : g ≤ 2*Real.pi/(k+1 : ℝ) := hs.trans (div_le_div_of_nonneg_left (by positivity) kpos grow)
  have lim : 2*Real.pi/(k+1 : ℝ) ≤ Real.pi := by
    apply (div_le_iff₀ kpos).mpr
    have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hkr)]
  have gc := cosBound.trans (Real.cos_le_cos_of_nonneg_of_le_pi h0 lim gs)
  let a := dist x z/d
  let b := dist y z/d
  have core := corner a (radii x hx) b (radii y hy)
  have ab : 0 ≤ 2*a*b := by dsimp [a,b]; positivity
  have unit : a^2+b^2-2*a*b*Real.cos g ≤ 1 := by linarith [mul_le_mul_of_nonneg_left gc ab]
  have id : dist x y ^ 2 = d^2*(a^2+b^2-2*a*b*Real.cos g) := by
    rw [polar_distance z x y, ←hg]; dsimp [a,b]; field_simp [hd.ne']
  have hit := mul_le_mul_of_nonneg_left unit (sq_nonneg d)
  have far := sep x hx y hy ne
  nlinarith only [hit,id,mul_pos (sub_pos.mpr far) (show 0 < dist x y+d by positivity)]

theorem annulus_card (P : Finset Plane) (z : Plane) {d l u : ℝ} (hd : 0 < d)
    (sep : separated P d) (hl : 0<l) (hu : 0<u) (radii : ∀ x ∈ P, dist x z/d ∈ Set.Icc l u)
    (fallback : ℕ) (hf : P.card ≤ fallback) : P.card ≤ annulusCap l u fallback := by
  classical
  unfold annulusCap
  dsimp only
  split
  next test =>
    let k := Nat.find test
    have pass := Nat.find_spec test
    change 4 ≤ k ∧ k ≤ 127 ∧ _ at pass
    let ψ : ℝ := 44/(7*((k:ℝ)+1))
    have hr : (4:ℝ) ≤ k := by exact_mod_cast pass.1
    have den : 0 < (k:ℝ)+1 := by positivity
    have upper : 2*Real.pi/(k+1:ℝ) ≤ ψ := by
      dsimp [ψ]; apply (div_le_div_iff₀ den (by positivity)).mpr
      have pi : 7*Real.pi < 22 := by linarith [Real.pi_lt_d4]
      nlinarith [mul_nonneg (sub_nonneg.mpr pi.le) den.le]
    have pos : 0 ≤ 2*Real.pi/(k+1:ℝ) := by positivity
    have top : ψ ≤ Real.pi := by
      dsimp [ψ]; apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hr),Real.pi_gt_three]
    apply radial_card P z hd sep (k:=k) (by omega) radii _ (fun a ha b hb ↦ corner_unit hl hu ha hb)
    exact (show annulusCosine l u ≤ 1-ψ^2/2+ψ^4/24-ψ^6/720 by simpa [ψ,k] using pass.2.2.le).trans
      ((cosine_poly ψ (pos.trans upper)).trans (Real.cos_le_cos_of_nonneg_of_le_pi pos top upper))
  next _ => exact hf

end
end HadwigerNelson.Packing

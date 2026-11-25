import Chowla.Amplitude
import Chowla.CountingDyadic
import Chowla.Variational

namespace Chowla

open Filter MeasureTheory
open scoped Topology

/-- Theorem 1 in a class, from the numerical certificate, the variational estimate for its
amplitude, and the two limits of the elementary squarefree count. -/
theorem main_class_of_variational_and_mass (hCertificate : CertificateStatement) (D : DiscClass)
    (hVariational : ∀ W : ShellWeight, ∀ ε > 0,
      ∀ᶠ X in atTop,
        (19 - Real.cot (1 / 4)) / 16 + inner_G F₈ - inner F₈ F₈ / 2 - ε ≤
          weightedAverage D W X nonvanishingIndicator)
    (hMass : ∀ W : ShellWeight,
      Tendsto (fun X => weightedSum D W X (fun _ => 1) / X) atTop
        (𝓝 (classDensity D * ∫ u : ℝ, W.toFun u)))
    (hShell : Tendsto (fun X => ((sharpShell D X).card : ℝ) / X) atTop (𝓝 (classDensity D))) :
    ClassStatement D := by
  let p := (19 - Real.cot (1 / 4)) / 16 + inner_G F₈ - inner F₈ F₈ / 2
  let q := (0.9453419890 + p) / 2
  have hp : 0.9453419890 < p := hCertificate
  have hq : q < p := by dsimp [q]; linarith
  have hq' : 0.9453419890 < q := by dsimp [q]; linarith
  exact ⟨q, hq', sharp_count_of_weighted_of_limits D p q hq hMass hShell hVariational⟩

/-- Assembly of Theorem 1 from the certificate, Theorem 22 and Lemma 8. -/
theorem main_of_variational_and_mass (hCertificate : CertificateStatement)
    (hVariational : ∀ (D : DiscClass) (W : ShellWeight) (F : Amplitude), IsAmplitude F →
      ∀ (z : ℝ) (ε : ℝ), 0 < ε →
        ∀ᶠ X in atTop,
          (19 - Real.cot (1 / 4)) / 16 + z * inner_G F - z^2 * inner F F / 2 - ε ≤
            weightedAverage D W X nonvanishingIndicator)
    (hMass : ∀ (D : DiscClass) (W : ShellWeight),
      Tendsto (fun X => weightedSum D W X (fun _ => 1) / X) atTop
        (𝓝 (classDensity D * ∫ u : ℝ, W.toFun u)) ∧
      Tendsto (fun X => ((sharpShell D X).card : ℝ) / X) atTop (𝓝 (classDensity D))) :
    MainStatement := by
  apply mainStatement_of_classStatements
  intro D
  refine main_class_of_variational_and_mass hCertificate D ?_ (fun W => (hMass D W).1) ?_
  · intro W ε hε
    simpa only [one_mul, one_pow] using hVariational D W F₈ final_amplitude_admissible 1 ε hε
  · obtain ⟨W, _, _⟩ := exists_shellWeight_large_integral (1 / 2) (by norm_num) (by norm_num)
    exact (hMass D W).2

theorem main_class_of_certificate_and_mass (hGRH : DirichletLZerosOnLine)
    (c : CitedFacts) (m : PaperClaims) (hCertificate : CertificateStatement) (D : DiscClass)
    (hMass : ∀ W : ShellWeight,
      Tendsto (fun X => weightedSum D W X (fun _ => 1) / X) atTop
        (𝓝 (classDensity D * ∫ u : ℝ, W.toFun u)) ∧
      Tendsto (fun X => ((sharpShell D X).card : ℝ) / X) atTop (𝓝 (classDensity D))) :
    ClassStatement D := by
  refine main_class_of_variational_and_mass hCertificate D ?_ (fun W => (hMass W).1) ?_
  · intro W ε hε
    simpa only [one_mul, one_pow] using
      variational hGRH c m D W F₈ final_amplitude_admissible 1 ε hε
  · obtain ⟨W, _, _⟩ := exists_shellWeight_large_integral (1 / 2) (by norm_num) (by norm_num)
    exact (hMass W).2

theorem main_of_certificate_and_mass (hGRH : DirichletLZerosOnLine)
    (c : CitedFacts) (m : PaperClaims) (hCertificate : CertificateStatement)
    (hMass : ∀ (D : DiscClass) (W : ShellWeight),
      Tendsto (fun X => weightedSum D W X (fun _ => 1) / X) atTop
        (𝓝 (classDensity D * ∫ u : ℝ, W.toFun u)) ∧
      Tendsto (fun X => ((sharpShell D X).card : ℝ) / X) atTop (𝓝 (classDensity D))) :
    MainStatement := by
  exact main_of_variational_and_mass hCertificate (variational hGRH c m) hMass

end Chowla

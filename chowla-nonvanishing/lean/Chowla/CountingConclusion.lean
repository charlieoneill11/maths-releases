import Chowla.CountingMain
import Chowla.CountingMass

namespace Chowla

open Filter MeasureTheory
open scoped Topology

/-- The difference between the sharp and smooth shell masses in Lemma 8. -/
theorem sharpShell_mass_deficit (D : DiscClass) (W : ShellWeight) :
    Tendsto (fun X : ℝ =>
      (((sharpShell D X).card : ℝ) - weightedSum D W X (fun _ => 1)) / X) atTop
      (𝓝 (classDensity D * (1 - ∫ u : ℝ, W.toFun u))) :=
  sharpShell_mass_deficit_of_limits D W (squarefree_shell_mass D W).1 (squarefree_shell_mass D W).2

theorem sharp_count_of_weighted (D : DiscClass) (p q : ℝ) (hq : q < p)
    (hweighted : ∀ W : ShellWeight, ∀ ε > 0, ∀ᶠ X in atTop,
      p - ε ≤ weightedAverage D W X nonvanishingIndicator) :
    ∀ᶠ X in atTop, q * ((classDiscs D X).card : ℝ) ≤
      ((nonvanishing (classDiscs D X)).card : ℝ) :=
  sharp_count_of_weighted_of_limits D p q hq (tendsto_weightedMass D)
    (tendsto_sharpShell_card D) hweighted

/-- The classwise Theorem 1 with the numerical comparison as an explicit premise. -/
theorem main_class_of_certificate (hGRH : DirichletLZerosOnLine) (c : CitedFacts) (m : PaperClaims)
    (hCertificate : CertificateStatement) (D : DiscClass) : ClassStatement D :=
  main_class_of_certificate_and_mass hGRH c m hCertificate D (squarefree_shell_mass D)

/-- Theorem 1 with the numerical comparison as an explicit premise. -/
theorem main_of_certificate (hGRH : DirichletLZerosOnLine) (c : CitedFacts) (m : PaperClaims)
    (hCertificate : CertificateStatement) : MainStatement :=
  main_of_certificate_and_mass hGRH c m hCertificate squarefree_shell_mass

end Chowla

import Chowla.CountingConclusion
import Chowla.StageCertificate

namespace Chowla

/-- The nonvanishing lower bound in each sign and 2-adic class, assuming the
stated GRH, cited facts, and the paper's empty-pattern moment theorem. -/
theorem main_class_of (hGRH : DirichletLZerosOnLine) (h : CitedFacts) (c : PaperClaims)
    (D : DiscClass) : ClassStatement D :=
  main_class_of_certificate hGRH h c certificate D

/-- The nonvanishing lower bound over all fundamental discriminants, subject
to the same number-theoretic inputs as the classwise result. -/
theorem main_of (hGRH : DirichletLZerosOnLine) (h : CitedFacts) (c : PaperClaims) :
    MainStatement :=
  main_of_certificate hGRH h c certificate

end Chowla

import LeastPrime.Checker.CertificateSound

namespace LeastPrime.Native

open Checker

theorem dm1420_lower_checked : checkWindow .lower 6 140000 200000 596755 = true := by
  native_decide

end LeastPrime.Native

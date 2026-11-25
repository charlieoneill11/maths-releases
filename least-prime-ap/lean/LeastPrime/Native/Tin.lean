import LeastPrime.Checker.CertificateSound

namespace LeastPrime.Native

open Checker

theorem tin_checked : checkWindow .lower 6 142858 199999 587142 = true := by
  native_decide

end LeastPrime.Native

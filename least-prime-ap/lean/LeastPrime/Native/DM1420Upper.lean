import LeastPrime.Checker.CertificateSound

namespace LeastPrime.Native

open Checker

theorem dm1420_upper_checked : checkWindow .upper 5 140000 200000 604658 = true := by
  native_decide

end LeastPrime.Native

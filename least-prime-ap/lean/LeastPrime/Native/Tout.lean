import LeastPrime.Checker.CertificateSound

namespace LeastPrime.Native

open Checker

theorem tout_checked : checkWindow .upper 5 142857 200000 595573 = true := by
  native_decide

end LeastPrime.Native

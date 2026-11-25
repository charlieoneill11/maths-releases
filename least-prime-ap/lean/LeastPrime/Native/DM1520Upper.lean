import LeastPrime.Checker.CertificateSound

namespace LeastPrime.Native

open Checker

theorem dm1520_upper_checked : checkWindow .upper 5 150000 200000 572090 = true := by
  native_decide

end LeastPrime.Native

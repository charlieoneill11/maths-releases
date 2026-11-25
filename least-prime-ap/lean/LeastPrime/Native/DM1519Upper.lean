import LeastPrime.Checker.CertificateSound

namespace LeastPrime.Native

open Checker

theorem dm1519_upper_checked : checkWindow .upper 5 150000 190000 544968 = true := by
  native_decide

end LeastPrime.Native

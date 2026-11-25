import LeastPrime.Checker.SliceSound

namespace LeastPrime.Native

open Checker

theorem dm1519_tail3_checked :
    checkLowerSlice true 150000 190000 947812 1000000 32018764650 = true := by
  native_decide

end LeastPrime.Native

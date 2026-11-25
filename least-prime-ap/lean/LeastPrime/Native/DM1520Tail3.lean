import LeastPrime.Checker.SliceSound

namespace LeastPrime.Native

open Checker

theorem dm1520_tail3_checked :
    checkLowerSlice true 150000 200000 947812 1000000 33295016154 = true := by
  native_decide

end LeastPrime.Native

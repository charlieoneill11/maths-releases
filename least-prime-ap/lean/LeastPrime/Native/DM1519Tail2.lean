import LeastPrime.Checker.SliceSound

namespace LeastPrime.Native

open Checker

theorem dm1519_tail2_checked :
    checkLowerSlice true 150000 190000 898906 947812 36359207937 = true := by
  native_decide

end LeastPrime.Native

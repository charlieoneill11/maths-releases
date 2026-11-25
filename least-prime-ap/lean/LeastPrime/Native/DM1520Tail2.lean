import LeastPrime.Checker.SliceSound

namespace LeastPrime.Native

open Checker

theorem dm1520_tail2_checked :
    checkLowerSlice true 150000 200000 898906 947812 37758395259 = true := by
  native_decide

end LeastPrime.Native

import LeastPrime.Checker.SliceSound

namespace LeastPrime.Native

open Checker

theorem dm1520_tail1_checked :
    checkLowerSlice true 150000 200000 850000 898906 42959261592 = true := by
  native_decide

end LeastPrime.Native

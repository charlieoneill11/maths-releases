import LeastPrime.Checker.SliceSound

namespace LeastPrime.Native

open Checker

theorem dm1520_interior3_checked :
    checkLowerSlice false 150000 200000 600140 800000 111569244120 = true := by
  native_decide

end LeastPrime.Native

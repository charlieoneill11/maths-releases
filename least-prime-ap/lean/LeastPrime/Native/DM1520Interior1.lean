import LeastPrime.Checker.SliceSound

namespace LeastPrime.Native

open Checker

theorem dm1520_interior1_checked :
    checkLowerSlice false 150000 200000 200000 400070 123389480097 = true := by
  native_decide

end LeastPrime.Native

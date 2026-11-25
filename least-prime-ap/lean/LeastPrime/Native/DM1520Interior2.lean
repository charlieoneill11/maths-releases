import LeastPrime.Checker.SliceSound

namespace LeastPrime.Native

open Checker

theorem dm1520_interior2_checked :
    checkLowerSlice false 150000 200000 400070 600140 113015399328 = true := by
  native_decide

end LeastPrime.Native

import LeastPrime.Checker.SliceSound

namespace LeastPrime.Native

open Checker

theorem dm1519_interior2_checked :
    checkLowerSlice false 150000 190000 390070 590140 106923912498 = true := by
  native_decide

end LeastPrime.Native

import LeastPrime.Checker.SliceSound

namespace LeastPrime.Native

open Checker

theorem dm1519_interior3_checked :
    checkLowerSlice false 150000 190000 590140 810000 115593539586 = true := by
  native_decide

end LeastPrime.Native

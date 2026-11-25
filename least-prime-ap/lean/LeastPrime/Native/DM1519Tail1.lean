import LeastPrime.Checker.SliceSound

namespace LeastPrime.Native

open Checker

theorem dm1519_tail1_checked :
    checkLowerSlice true 150000 190000 850000 898906 41721766398 = true := by
  native_decide

end LeastPrime.Native

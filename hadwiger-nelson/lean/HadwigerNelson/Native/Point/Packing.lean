import HadwigerNelson.Certificate.Hole.Pack

namespace HadwigerNelson.Certificate.Hole

/-- The 16,384 angular bins satisfy all four rational packing bounds for L,
T, U and J, using the verified pointwise neighbour cap for every bin. -/
theorem packing_checked : checkPacking = true := by native_decide

end HadwigerNelson.Certificate.Hole

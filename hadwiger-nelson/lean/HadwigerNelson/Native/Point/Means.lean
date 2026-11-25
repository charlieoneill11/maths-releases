import HadwigerNelson.Certificate.Hole.TableSound

namespace HadwigerNelson.Certificate.Hole

/-- Exact evaluation of the 16,384 unit bins and both sets of 8,192 short
bins, including the two retained fractions. -/
theorem means_checked : checkMeans = true := by native_decide

end HadwigerNelson.Certificate.Hole

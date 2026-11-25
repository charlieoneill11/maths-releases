import HadwigerNelson.Stars.Partial.CertificateRuntime

namespace HadwigerNelson.Stars.PartialCheck.Native

/-- Check all 3,171 threshold queries on signed source indices 105,000 through 132,620 and the 4,122 native sources at degrees 1 through 89. -/
theorem shard3 : checkShard 3 = true := by native_decide

end HadwigerNelson.Stars.PartialCheck.Native

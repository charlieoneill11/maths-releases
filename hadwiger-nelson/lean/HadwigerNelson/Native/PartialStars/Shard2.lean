import HadwigerNelson.Stars.Partial.CertificateRuntime

namespace HadwigerNelson.Stars.PartialCheck.Native

/-- Check all 3,171 threshold queries on signed source indices 70,000 through 104,999. -/
theorem shard2 : checkShard 2 = true := by native_decide

end HadwigerNelson.Stars.PartialCheck.Native

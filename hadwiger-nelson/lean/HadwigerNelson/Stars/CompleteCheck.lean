import HadwigerNelson.Stars.CreditRuntime

namespace HadwigerNelson.Stars.BoxCheck

/-- Evaluate the fixed complete-wave data when its certificate is requested. -/
def checkComplete : Bool :=
  let arcs := arcTable
  checkData (rowRange arcs 0 14464) (saturatedData arcs)

end HadwigerNelson.Stars.BoxCheck

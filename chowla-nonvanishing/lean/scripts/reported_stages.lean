import Chowla.StageData
import Chowla.StageData.Stage4
import Chowla.StageData.Stage5
import Chowla.StageData.Stage6
import Chowla.StageData.Stage7
import Chowla.StageData.Stage8

open Chowla Chowla.Checker

private def serialize (x : ℚ) : String := s!"{x.num}/{x.den}"

private def printEarly (b : StageBounds) : IO Unit := do
  let proportion := p₀ + b.lowerCentral ^ 2 / (2 * b.upperGram)
  IO.println (String.intercalate " " ([b.lowerCentral, b.upperCentral, b.upperGram, proportion].map serialize))

def main : IO Unit := do
  for b in [reportedStage1, reportedStage2, reportedStage3, reportedStage4] do
    printEarly b
  for b in [reportedStage5, reportedStage6, reportedStage7, reportedStage8] do
    IO.println (serialize b.lowerProportion)

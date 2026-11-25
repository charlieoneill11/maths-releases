import HadwigerNelson.Wave.Geometry.CellVolume
import Mathlib.MeasureTheory.Group.FundamentalDomain

namespace HadwigerNelson.Wave
open MeasureTheory

theorem lattice_fundamental (W : Datum) : IsAddFundamentalDomain (lattice W) (cell W (3*H)) volume :=
  IsAddFundamentalDomain.mk' (cell_measurable ..).nullMeasurableSet (lattice_cell_rep W)

theorem holeLattice_fundamental (W : Datum) : IsAddFundamentalDomain (holeLattice W) (cell W H) volume :=
  IsAddFundamentalDomain.mk' (cell_measurable ..).nullMeasurableSet (holeLattice_cell_rep W)

end HadwigerNelson.Wave

import Definitions.Def_JuilletCanonicalRoutes

open MeasureTheory

open ConcaveOTLimit

theorem solution
    (mu nu : FiniteMeasure Real) (h x y y' : Real)
    (hxy : AreConsecutiveAtLevel mu nu h x y)
    (hxy' : AreConsecutiveAtLevel mu nu h x y') :
    y = y' := by
  apply le_antisymm
  · exact le_of_not_gt fun hy'y =>
      hxy.2.2.2 y' ⟨hxy'.1, hy'y⟩ hxy'.2.2.1
  · exact le_of_not_gt fun hyy' =>
      hxy'.2.2.2 y ⟨hxy.1, hyy'⟩ hxy.2.2.1

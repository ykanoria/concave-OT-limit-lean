import Definitions.Def_JuilletCanonicalRoutes

open MeasureTheory

namespace ConcaveOTLimit

/-- The right endpoint consecutive to a fixed left endpoint at a fixed level
is unique. -/
theorem consecutiveAtLevelRightUnique
    (mu nu : FiniteMeasure Real) (h x y y' : Real)
    (hxy : AreConsecutiveAtLevel mu nu h x y)
    (hxy' : AreConsecutiveAtLevel mu nu h x y') :
    y = y' := by
  rcases lt_trichotomy y y' with hyy' | rfl | hy'y
  · exact
      (hxy'.2.2.2 y ⟨hxy.1, hyy'⟩ hxy.2.2.1).elim
  · rfl
  · exact
      (hxy.2.2.2 y' ⟨hxy'.1, hy'y⟩ hxy'.2.2.1).elim

end ConcaveOTLimit

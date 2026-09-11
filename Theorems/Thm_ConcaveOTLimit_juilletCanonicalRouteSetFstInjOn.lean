import Theorems.Thm_ConcaveOTLimit_goodIncreasingCrossingLevelEqOfAtomlessAt
import Theorems.Thm_ConcaveOTLimit_consecutiveAtLevelRightUnique

open MeasureTheory Set

namespace ConcaveOTLimit

/-- When the source is atomless, each source point has at most one canonical
Juillet route endpoint. -/
theorem juilletCanonicalRouteSetFstInjOn
    (mu nu : FiniteMeasure Real)
    (hAtomless : IsAtomlessFinite mu) :
    Set.InjOn Prod.fst (juilletCanonicalRouteSet mu nu) := by
  intro p hp q hq hfst
  rcases hp with
    ⟨h, _hPos, hIncreasing, _hDecreasing, hConsecutive⟩
  rcases hq with
    ⟨h', _hPos', hIncreasing', _hDecreasing', hConsecutive'⟩
  have hLevel : h = h' := by
    calc
      h = signedCumulative mu nu p.1 :=
        goodIncreasingCrossingLevelEqOfAtomlessAt
          mu nu p.1 h (hAtomless p.1) hIncreasing
      _ = signedCumulative mu nu q.1 :=
        congrArg (signedCumulative mu nu) hfst
      _ = h' :=
        (goodIncreasingCrossingLevelEqOfAtomlessAt
          mu nu q.1 h' (hAtomless q.1) hIncreasing').symm
  have hConsecutive'' :
      AreConsecutiveAtLevel mu nu h p.1 q.2 := by
    rw [hLevel, hfst]
    exact hConsecutive'
  have hsnd : p.2 = q.2 :=
    consecutiveAtLevelRightUnique
      mu nu h p.1 p.2 q.2 hConsecutive hConsecutive''
  exact Prod.ext hfst hsnd

end ConcaveOTLimit

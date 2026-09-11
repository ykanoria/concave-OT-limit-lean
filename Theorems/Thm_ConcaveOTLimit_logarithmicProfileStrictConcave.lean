import Definitions.Def_ConcaveOTLimitModel

open Set

namespace ConcaveOTLimit

/-- The logarithmic secondary profile is strictly concave on the
nonnegative half-line. -/
theorem logarithmicProfileStrictConcave :
    StrictConcaveOn Real (Ici 0) logarithmicProfile := by
  unfold logarithmicProfile
  exact Real.strictConcaveOn_negMulLog

end ConcaveOTLimit

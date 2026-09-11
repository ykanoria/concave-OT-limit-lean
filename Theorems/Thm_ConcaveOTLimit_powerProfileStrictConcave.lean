import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic.Linarith

open Set

namespace ConcaveOTLimit

/-- Every power profile with parameter in the perturbation domain is strictly
concave on the nonnegative half-line. -/
theorem powerProfileStrictConcave
    {epsilon : Real} (hEpsilon : epsilon ∈ epsilonDomain) :
    StrictConcaveOn Real (Ici 0) (powerProfile epsilon) := by
  unfold powerProfile
  exact Real.strictConcaveOn_rpow (by linarith [hEpsilon.2])
    (by linarith [hEpsilon.1])

end ConcaveOTLimit

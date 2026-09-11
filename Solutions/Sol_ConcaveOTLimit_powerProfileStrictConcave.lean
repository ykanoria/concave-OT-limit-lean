import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic.Linarith

open Set

open ConcaveOTLimit

theorem solution
    {epsilon : Real} (hEpsilon : epsilon ∈ epsilonDomain) :
    StrictConcaveOn Real (Ici 0) (powerProfile epsilon) := by
  unfold powerProfile
  exact Real.strictConcaveOn_rpow (by linarith [hEpsilon.2])
    (by linarith [hEpsilon.1])

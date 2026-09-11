import Theorems.Thm_ConcaveOTLimit_forwardSecondaryMinimizerEqExcursionCoupling
import Theorems.Thm_ConcaveOTLimit_juilletExcursionForwardAndDistanceOptimalFace
import Theorems.Thm_ConcaveOTLimit_oneDimensionalExcursionVariationalOfStrictIdentification

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    {mu nu : FiniteMeasure Real}
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (gammaEC : FiniteCoupling mu nu)
    (hEC : IsJuilletExcursionPlan mu nu gammaEC.plan)
    (hSupportProduction :
      forall profile : Real -> Real,
        AdmissibleStrictlyConcaveProfile profile ->
          forall gamma : FiniteCoupling mu nu,
            IsSecondaryMinimizer profile gamma ->
            IsForwardPlan gamma ->
            exists support : Set (Real × Real),
              MeasurableSet support /\
              IsSupported gamma support /\
              forall {x y x' y' : Real},
                (x, y) ∈ support -> (x', y') ∈ support ->
                  dist x y + dist x' y' <=
                      dist x y' + dist x' y /\
                    (dist x y + dist x' y' =
                        dist x y' + dist x' y ->
                      profile (dist x y) + profile (dist x' y') <=
                        profile (dist x y') + profile (dist x' y)))
    (hJuilletIdentification :
      forall gamma : FiniteCoupling mu nu,
        IsJuilletExcursionPlan mu nu gamma.plan ->
          gamma = gammaEC) :
    IsForwardPlan gammaEC /\
      {gamma : FiniteCoupling mu nu | IsForwardPlan gamma} =
        distanceOptimalFace mu nu /\
      (forall profile : Real -> Real,
        AdmissibleConcaveProfile profile ->
          IsMinimizerOn
            {gamma : FiniteCoupling mu nu | IsForwardPlan gamma}
            (profileCost profile) gammaEC) /\
      (forall profile : Real -> Real,
        AdmissibleStrictlyConcaveProfile profile ->
          IsUniqueMinimizerOn
            {gamma : FiniteCoupling mu nu | IsForwardPlan gamma}
            (profileCost profile) gammaEC) := by
  rcases juilletExcursionForwardAndDistanceOptimalFace
      hFirstMu hFirstNu hAtomless hOrder gammaEC hEC with
    ⟨_hForwardEC, hForwardFace⟩
  refine oneDimensionalExcursionVariationalOfStrictIdentification
    hFirstMu hFirstNu hAtomless hOrder gammaEC hEC ?_
  intro profile hProfile gamma hGammaMinimizer
  have hSecondary : IsSecondaryMinimizer profile gamma := by
    change
      IsMinimizerOn (distanceOptimalFace mu nu)
        (profileCost profile) gamma
    rw [← hForwardFace]
    exact hGammaMinimizer
  exact forwardSecondaryMinimizerEqExcursionCoupling
    gammaEC hProfile.1 hSingular
    (hSupportProduction profile hProfile)
    hJuilletIdentification gamma hSecondary hGammaMinimizer.1

import Theorems.Thm_ConcaveOTLimit_isJuilletExcursionPlanOfLexicographicSupport

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    {mu nu : FiniteMeasure Real}
    {profile : Real -> Real}
    (gammaEC : FiniteCoupling mu nu)
    (hProfile : StrictConcaveOn Real (Ici 0) profile)
    (hSingular : FiniteMutuallySingular mu nu)
    (hSupportProduction :
      forall gamma : FiniteCoupling mu nu,
        IsSecondaryMinimizer profile gamma ->
        IsForwardPlan gamma ->
        exists support : Set (Real × Real),
          MeasurableSet support /\
          IsSupported gamma support /\
          forall {x y x' y' : Real},
            (x, y) ∈ support -> (x', y') ∈ support ->
              dist x y + dist x' y' <= dist x y' + dist x' y /\
              (dist x y + dist x' y' = dist x y' + dist x' y ->
                profile (dist x y) + profile (dist x' y') <=
                  profile (dist x y') + profile (dist x' y)))
    (hJuilletIdentification :
      forall gamma : FiniteCoupling mu nu,
        IsJuilletExcursionPlan mu nu gamma.plan ->
          gamma = gammaEC) :
    forall gamma : FiniteCoupling mu nu,
      IsSecondaryMinimizer profile gamma ->
      IsForwardPlan gamma ->
      gamma = gammaEC := by
  intro gamma hMinimizer hForward
  obtain ⟨support, hMeasurable, hFull, hLex⟩ :=
    hSupportProduction gamma hMinimizer hForward
  apply hJuilletIdentification gamma
  exact isJuilletExcursionPlanOfLexicographicSupport
    hProfile hSingular hForward hMeasurable hFull hLex

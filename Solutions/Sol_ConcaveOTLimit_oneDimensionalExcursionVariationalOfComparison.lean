import Theorems.Thm_ConcaveOTLimit_juilletExcursionForwardAndDistanceOptimalFace

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    {mu nu : FiniteMeasure Real}
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (gammaEC : FiniteCoupling mu nu)
    (hEC : IsJuilletExcursionPlan mu nu gammaEC.plan)
    (hComparison :
      forall profile : Real -> Real,
        AdmissibleConcaveProfile profile ->
          forall gamma : FiniteCoupling mu nu,
            IsForwardPlan gamma ->
              profileCost profile gammaEC <= profileCost profile gamma)
    (hStrictRigidity :
      forall profile : Real -> Real,
        AdmissibleStrictlyConcaveProfile profile ->
          forall gamma : FiniteCoupling mu nu,
            IsForwardPlan gamma ->
              profileCost profile gammaEC = profileCost profile gamma ->
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
    ⟨hForwardEC, hForwardFace⟩
  refine ⟨hForwardEC, hForwardFace, ?_, ?_⟩
  · intro profile hProfile
    constructor
    · exact hForwardEC
    · intro gamma hForward
      exact hComparison profile hProfile gamma hForward
  · intro profile hStrictProfile
    have hProfile : AdmissibleConcaveProfile profile :=
      ⟨hStrictProfile.1.concaveOn, hStrictProfile.2⟩
    constructor
    · exact ⟨hForwardEC, fun gamma hForward =>
        hComparison profile hProfile gamma hForward⟩
    · intro gamma hGammaMinimizer
      have hECLe :
          profileCost profile gammaEC <= profileCost profile gamma :=
        hComparison profile hProfile gamma hGammaMinimizer.1
      have hGammaLe :
          profileCost profile gamma <= profileCost profile gammaEC :=
        hGammaMinimizer.2 gammaEC hForwardEC
      exact hStrictRigidity profile hStrictProfile gamma
        hGammaMinimizer.1 (le_antisymm hECLe hGammaLe)

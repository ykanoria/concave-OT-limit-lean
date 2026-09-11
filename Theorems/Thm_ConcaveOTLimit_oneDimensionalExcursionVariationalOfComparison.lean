import Theorems.Thm_ConcaveOTLimit_juilletExcursionForwardAndDistanceOptimalFace

open MeasureTheory Set

namespace ConcaveOTLimit

/-- The one-dimensional excursion variational theorem follows from the
profile comparison and strict equality-rigidity properties on forward
couplings. -/
theorem oneDimensionalExcursionVariationalOfComparison
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
  obtain ⟨hForwardEC, hForwardFace⟩ :=
    juilletExcursionForwardAndDistanceOptimalFace
      hFirstMu hFirstNu hAtomless hOrder gammaEC hEC
  refine ⟨hForwardEC, hForwardFace, ?_, ?_⟩
  · intro profile hProfile
    exact ⟨hForwardEC, fun gamma hForward =>
      hComparison profile hProfile gamma hForward⟩
  · intro profile hProfile
    have hConcaveProfile : AdmissibleConcaveProfile profile :=
      ⟨hProfile.1.concaveOn, hProfile.2⟩
    have hMinimizer :
        IsMinimizerOn
          {gamma : FiniteCoupling mu nu | IsForwardPlan gamma}
          (profileCost profile) gammaEC :=
      ⟨hForwardEC, fun gamma hForward =>
        hComparison profile hConcaveProfile gamma hForward⟩
    refine ⟨hMinimizer, ?_⟩
    intro gamma hGammaMinimizer
    apply hStrictRigidity profile hProfile gamma hGammaMinimizer.1
    exact le_antisymm
      (hComparison profile hConcaveProfile gamma hGammaMinimizer.1)
      (hGammaMinimizer.2 gammaEC hForwardEC)

end ConcaveOTLimit

import Theorems.Thm_ConcaveOTLimit_existsAdmissibleConcaveForwardMinimizer
import Theorems.Thm_ConcaveOTLimit_concaveComparison_of_strictPowerHalfIdentification
import Theorems.Thm_ConcaveOTLimit_oneDimensionalExcursionVariationalOfComparison

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
    (hStrictIdentification :
      forall profile : Real -> Real,
        AdmissibleStrictlyConcaveProfile profile ->
          forall gamma : FiniteCoupling mu nu,
            IsMinimizerOn
              {eta : FiniteCoupling mu nu | IsForwardPlan eta}
              (profileCost profile) gamma ->
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
  have hForwardEC : IsForwardPlan gammaEC :=
    isForwardPlanOfJuilletExcursionPlan hAtomless hOrder hEC
  have hMu :
      Integrable (fun x : Real => x) (mu : Measure Real) := by
    apply (integrable_norm_iff continuous_id.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using hFirstMu
  have hNu :
      Integrable (fun y : Real => y) (nu : Measure Real) := by
    apply (integrable_norm_iff continuous_id.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using hFirstNu
  have hStrictMinimality :
      forall profile : Real -> Real,
        AdmissibleStrictlyConcaveProfile profile ->
          IsMinimizerOn
            {eta : FiniteCoupling mu nu | IsForwardPlan eta}
            (profileCost profile) gammaEC := by
    intro profile hStrictProfile
    have hProfile : AdmissibleConcaveProfile profile :=
      ⟨hStrictProfile.1.concaveOn, hStrictProfile.2⟩
    rcases existsAdmissibleConcaveForwardMinimizer
        hProfile hMu hNu gammaEC hForwardEC with
      ⟨gamma, hGammaMinimizer⟩
    rw [hStrictIdentification profile hStrictProfile gamma hGammaMinimizer]
      at hGammaMinimizer
    exact hGammaMinimizer
  have hComparison :
      forall profile : Real -> Real,
        AdmissibleConcaveProfile profile ->
          forall gamma : FiniteCoupling mu nu,
            IsForwardPlan gamma ->
              profileCost profile gammaEC <= profileCost profile gamma :=
    concaveComparison_of_strictPowerHalfIdentification
      hFirstMu hFirstNu gammaEC hStrictMinimality
  have hStrictRigidity :
      forall profile : Real -> Real,
        AdmissibleStrictlyConcaveProfile profile ->
          forall gamma : FiniteCoupling mu nu,
            IsForwardPlan gamma ->
              profileCost profile gammaEC = profileCost profile gamma ->
                gamma = gammaEC := by
    intro profile hStrictProfile gamma hGammaForward hCostEq
    apply hStrictIdentification profile hStrictProfile gamma
    constructor
    · exact hGammaForward
    · intro eta hEtaForward
      rw [← hCostEq]
      exact (hStrictMinimality profile hStrictProfile).2 eta hEtaForward
  exact oneDimensionalExcursionVariationalOfComparison
    hFirstMu hFirstNu hAtomless hOrder gammaEC hEC
    hComparison hStrictRigidity

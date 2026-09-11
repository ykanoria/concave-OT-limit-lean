import Theorems.Thm_ConcaveOTLimit_existsForwardCouplingOfStochasticOrder
import Theorems.Thm_ConcaveOTLimit_existsJuilletExcursionPlanOfForwardCoupling
import Theorems.Thm_ConcaveOTLimit_oneDimensionalExcursionVariational

open MeasureTheory Set

namespace ConcaveOTLimit

/-- Under the hypotheses of paper Theorem 5, there exists a forward
finite coupling satisfying Juillet's monotone-arch excursion condition. -/
theorem existsJuilletExcursionPlan
    (mu nu : FiniteMeasure Real)
    (hMass : mu.mass = nu.mass)
    (_hPositive : 0 < mu.mass)
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hSingular : FiniteMutuallySingular mu nu)
    (_hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu) :
    exists gamma : FiniteCoupling mu nu,
      IsForwardPlan gamma /\
        IsJuilletExcursionPlan mu nu gamma.plan := by
  obtain ⟨gammaForward, hForward⟩ :=
    existsForwardCouplingOfStochasticOrder hMass hOrder
  exact
    existsJuilletExcursionPlanOfForwardCoupling
      hFirstMu hFirstNu hSingular gammaForward hForward

/-- Under the hypotheses of paper Theorem 5, two Juillet excursion
couplings of the same marginals are equal. -/
theorem juilletExcursionPlan_unique
    (mu nu : FiniteMeasure Real)
    (hMass : mu.mass = nu.mass)
    (hPositive : 0 < mu.mass)
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (gamma eta : FiniteCoupling mu nu)
    (hGamma : IsJuilletExcursionPlan mu nu gamma.plan)
    (hEta : IsJuilletExcursionPlan mu nu eta.plan) :
    gamma = eta := by
  exact
    monotoneArchPlan_unique
      hAtomless hOrder gamma eta hGamma hEta

/-- Under the hypotheses of paper Theorem 5, there is a unique forward
finite coupling satisfying Juillet's excursion condition. -/
theorem existsUniqueJuilletExcursionPlan
    (mu nu : FiniteMeasure Real)
    (hMass : mu.mass = nu.mass)
    (hPositive : 0 < mu.mass)
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu) :
    ∃! gamma : FiniteCoupling mu nu,
      IsForwardPlan gamma /\
        IsJuilletExcursionPlan mu nu gamma.plan := by
  obtain ⟨gamma, hForward, hExcursion⟩ :=
    existsJuilletExcursionPlan
      mu nu hMass hPositive hFirstMu hFirstNu hSingular hAtomless hOrder
  refine ⟨gamma, ⟨hForward, hExcursion⟩, ?_⟩
  intro eta hEta
  exact
    juilletExcursionPlan_unique
      mu nu hMass hPositive hFirstMu hFirstNu hSingular hAtomless hOrder
      eta gamma hEta.2 hExcursion

end ConcaveOTLimit

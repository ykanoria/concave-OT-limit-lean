import Theorems.Thm_ConcaveOTLimit_existsJuilletExcursionPlan
import Theorems.Thm_ConcaveOTLimit_isGraphPlanMapUniqueAe
import Theorems.Thm_ConcaveOTLimit_juilletExcursionPlanIsGraph

open MeasureTheory

namespace ConcaveOTLimit

/-- Paper Theorem 5: under equal positive mass, finite first moments,
mutual singularity, source atomlessness, and stochastic order, the unique
Juillet excursion coupling is forward and induced by a measurable map. -/
theorem existsJuilletExcursionMapCoupling
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
    exists (gammaEC : FiniteCoupling mu nu) (T : Real -> Real),
      IsGraphPlan gammaEC T /\
        IsForwardPlan gammaEC /\
        IsJuilletExcursionPlan mu nu gammaEC.plan /\
        (forall gamma : FiniteCoupling mu nu,
          IsJuilletExcursionPlan mu nu gamma.plan ->
            gamma = gammaEC) /\
        forall S, IsGraphPlan gammaEC S ->
          S =ᵐ[(mu : Measure Real)] T := by
  obtain ⟨gammaEC, hForward, hExcursion⟩ :=
    existsJuilletExcursionPlan
      mu nu hMass hPositive hFirstMu hFirstNu hSingular hAtomless hOrder
  obtain ⟨T, hGraph⟩ :=
    juilletExcursionPlanIsGraph
      gammaEC hSingular hAtomless hOrder hExcursion
  refine ⟨gammaEC, T, hGraph, hForward, hExcursion, ?_, ?_⟩
  intro gamma hGamma
  exact
    juilletExcursionPlan_unique
      mu nu hMass hPositive hFirstMu hFirstNu hSingular hAtomless hOrder
      gamma gammaEC hGamma hExcursion
  intro S hS
  exact isGraphPlan_map_unique_ae hGraph hS

end ConcaveOTLimit

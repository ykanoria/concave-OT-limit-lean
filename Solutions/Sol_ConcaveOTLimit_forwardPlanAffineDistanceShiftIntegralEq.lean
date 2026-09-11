import Theorems.Thm_ConcaveOTLimit_distanceCostEqMomentDifferenceIffForward
import Theorems.Thm_ConcaveOTLimit_distanceIntegrableOfMarginalFirstMoments

open MeasureTheory

open ConcaveOTLimit

private theorem measurePreservingFst
    {mu nu : FiniteMeasure Real} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.fst
      (gamma.plan : Measure (Real × Real)) (mu : Measure Real) := by
  refine ⟨measurable_fst, ?_⟩
  simpa [firstMarginal] using congrArg
    (fun measure : FiniteMeasure Real => (measure : Measure Real))
    gamma.property.1

private theorem planRealUnivEqSourceRealUniv
    {mu nu : FiniteMeasure Real} (gamma : FiniteCoupling mu nu) :
    (gamma.plan : Measure (Real × Real)).real Set.univ =
      (mu : Measure Real).real Set.univ := by
  rw [← (measurePreservingFst gamma).map_eq,
    map_measureReal_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ]

theorem solution
    {mu nu : FiniteMeasure Real}
    (hMu : Integrable (fun x : Real => x) (mu : Measure Real))
    (hNu : Integrable (fun y : Real => y) (nu : Measure Real))
    (gamma eta : FiniteCoupling mu nu)
    (hGamma : IsForwardPlan gamma)
    (hEta : IsForwardPlan eta)
    (C : Real) :
    (∫ z, C * (1 + ‖z.1 - z.2‖)
        ∂(gamma.plan : Measure (Real × Real))) =
      ∫ z, C * (1 + ‖z.1 - z.2‖)
        ∂(eta.plan : Measure (Real × Real)) := by
  have hMuNorm :
      Integrable (fun x : Real => ‖x‖) (mu : Measure Real) := by
    simpa using hMu.norm
  have hNuNorm :
      Integrable (fun y : Real => ‖y‖) (nu : Measure Real) := by
    simpa using hNu.norm
  have hGammaDistance :
      Integrable (fun z : Real × Real => ‖z.1 - z.2‖)
        (gamma.plan : Measure (Real × Real)) :=
    distanceIntegrableOfMarginalFirstMoments hMuNorm hNuNorm gamma
  have hEtaDistance :
      Integrable (fun z : Real × Real => ‖z.1 - z.2‖)
        (eta.plan : Measure (Real × Real)) :=
    distanceIntegrableOfMarginalFirstMoments hMuNorm hNuNorm eta
  have hDistanceCost :
      distanceCost gamma = distanceCost eta := by
    rw [
      (distanceCostEqMomentDifferenceIffForward gamma hMu hNu).mpr
        hGamma,
      (distanceCostEqMomentDifferenceIffForward eta hMu hNu).mpr hEta]
  have hGammaIntegral :
      (∫ z, C * (1 + ‖z.1 - z.2‖)
          ∂(gamma.plan : Measure (Real × Real))) =
        C * ((gamma.plan : Measure (Real × Real)).real Set.univ +
          distanceCost gamma) := by
    rw [integral_const_mul,
      integral_add (integrable_const 1) hGammaDistance, integral_const]
    simp [distanceCost, profileCost]
  have hEtaIntegral :
      (∫ z, C * (1 + ‖z.1 - z.2‖)
          ∂(eta.plan : Measure (Real × Real))) =
        C * ((eta.plan : Measure (Real × Real)).real Set.univ +
          distanceCost eta) := by
    rw [integral_const_mul,
      integral_add (integrable_const 1) hEtaDistance, integral_const]
    simp [distanceCost, profileCost]
  calc
    (∫ z, C * (1 + ‖z.1 - z.2‖)
        ∂(gamma.plan : Measure (Real × Real))) =
        C * ((gamma.plan : Measure (Real × Real)).real Set.univ +
          distanceCost gamma) := hGammaIntegral
    _ = C * ((mu : Measure Real).real Set.univ +
          distanceCost gamma) := by
      rw [planRealUnivEqSourceRealUniv gamma]
    _ = C * ((mu : Measure Real).real Set.univ +
          distanceCost eta) := by
      rw [hDistanceCost]
    _ = C * ((eta.plan : Measure (Real × Real)).real Set.univ +
          distanceCost eta) := by
      rw [planRealUnivEqSourceRealUniv eta]
    _ = ∫ z, C * (1 + ‖z.1 - z.2‖)
          ∂(eta.plan : Measure (Real × Real)) :=
      hEtaIntegral.symm

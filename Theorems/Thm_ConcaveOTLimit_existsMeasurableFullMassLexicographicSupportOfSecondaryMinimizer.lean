import Theorems.Thm_ConcaveOTLimit_existsForwardReroutingOfFailedSwap
import Theorems.Thm_ConcaveOTLimit_existsMeasurableStrictForwardTopologicalSupportOnCarrier
import Theorems.Thm_ConcaveOTLimit_forwardPairsDistanceTwoCycleAndReroutingOfTie
import Theorems.Thm_ConcaveOTLimit_forwardPlansEqDistanceOptimalFaceOfAbsMoments

open MeasureTheory Set

namespace ConcaveOTLimit

/-- A forward secondary minimizer with mutually singular marginals has a
measurable full-mass lexicographic support. The support is selected inside a
fixed source-target singularity carrier, so failed tied swaps permit forward
local reroutings. -/
theorem existsMeasurableFullMassLexicographicSupportOfSecondaryMinimizer
    {mu nu : FiniteMeasure Real}
    {gamma : FiniteCoupling mu nu}
    {profile : Real -> Real}
    (hProfile : AdmissibleStrictlyConcaveProfile profile)
    (hMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hSingular : FiniteMutuallySingular mu nu)
    (hMin : IsSecondaryMinimizer profile gamma)
    (hForward : IsForwardPlan gamma) :
    exists support : Set (Real × Real),
      MeasurableSet support /\
      IsSupported gamma support /\
      forall {x y x' y' : Real},
        (x, y) ∈ support -> (x', y') ∈ support ->
          dist x y + dist x' y' <= dist x y' + dist x' y /\
          (dist x y + dist x' y' = dist x y' + dist x' y ->
            profile (dist x y) + profile (dist x' y') <=
              profile (dist x y') + profile (dist x' y)) := by
  obtain ⟨A, hA, hMuCarrier, hNuCarrier⟩ := hSingular
  obtain
      ⟨support, hMeasurable, hSupported, hStrict, hCarrierSupport⟩ :=
    existsMeasurableStrictForwardTopologicalSupportOnCarrier
      hA hMuCarrier hNuCarrier hForward
  have hForwardFace :
      {eta : FiniteCoupling mu nu | IsForwardPlan eta} =
        distanceOptimalFace mu nu :=
    forwardPlansEqDistanceOptimalFaceOfAbsMoments
      hMu hNu gamma hForward
  refine ⟨support, hMeasurable, hSupported, ?_⟩
  intro x y x' y' hxy hx'y'
  have hxyData := hCarrierSupport hxy
  have hx'y'Data := hCarrierSupport hx'y'
  have hxyForward : x < y := hStrict hxy
  have hx'y'Forward : x' < y' := hStrict hx'y'
  refine
    ⟨(forwardPairsDistanceTwoCycleAndReroutingOfTie
      hxyForward.le hx'y'Forward.le).1, ?_⟩
  intro hTie
  by_contra hSecondary
  have hFailure :
      profile (dist x y') + profile (dist x' y) <
        profile (dist x y) + profile (dist x' y') :=
    lt_of_not_ge hSecondary
  obtain ⟨eta, hEtaForward, hEtaCheaper⟩ :=
    existsForwardReroutingOfFailedSwap
      hProfile hMu hNu hForward
      hxyData.1 hx'y'Data.1 hxyData.2 hx'y'Data.2
      hxyForward hx'y'Forward hTie hFailure
  have hEtaOptimal : eta ∈ distanceOptimalFace mu nu := by
    rw [← hForwardFace]
    exact hEtaForward
  exact (not_lt_of_ge (hMin.2 eta hEtaOptimal)) hEtaCheaper

end ConcaveOTLimit

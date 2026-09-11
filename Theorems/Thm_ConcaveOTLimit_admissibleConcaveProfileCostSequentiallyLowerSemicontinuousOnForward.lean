import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileCostLowerSemicontinuousAlongFilter

open Filter MeasureTheory Topology

namespace ConcaveOTLimit

/-- Sequential specialization of admissible-profile lower semicontinuity
on forward couplings. -/
theorem admissibleConcaveProfileCostSequentiallyLowerSemicontinuousOnForward
    {mu nu : FiniteMeasure Real}
    {profile : Real -> Real}
    (hProfile : AdmissibleConcaveProfile profile)
    (hMu : Integrable (fun x : Real => x) (mu : Measure Real))
    (hNu : Integrable (fun y : Real => y) (nu : Measure Real))
    {gammaSeq : Nat -> FiniteCoupling mu nu}
    {gamma : FiniteCoupling mu nu}
    (hTendsto : Tendsto gammaSeq atTop (nhds gamma))
    (hGammaForward : IsForwardPlan gamma)
    (hSeqForward : forall k, IsForwardPlan (gammaSeq k)) :
    ∀ r < profileCost profile gamma,
      ∀ᶠ k in atTop, r <= profileCost profile (gammaSeq k) := by
  intro r hr
  exact admissibleConcaveProfileCostLowerSemicontinuousAlongFilter
    hProfile hMu hNu hTendsto hGammaForward hSeqForward r hr

end ConcaveOTLimit

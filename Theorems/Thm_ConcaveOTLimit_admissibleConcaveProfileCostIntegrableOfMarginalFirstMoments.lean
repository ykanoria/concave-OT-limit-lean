import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileLinearGrowth
import Theorems.Thm_ConcaveOTLimit_concaveProfileDistanceLowerSemicontinuous
import Theorems.Thm_ConcaveOTLimit_distanceIntegrableOfMarginalFirstMoments

open MeasureTheory

namespace ConcaveOTLimit

/-- Every admissible concave profile cost is integrable under a finite
coupling whose marginals have finite first moments. -/
theorem admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    {profile : Real -> Real}
    (hProfile : AdmissibleConcaveProfile profile)
    (hMu : Integrable (fun x : E => ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => ‖y‖) (nu : Measure E))
    (gamma : FiniteCoupling mu nu) :
    Integrable (fun z : E × E => profile ‖z.1 - z.2‖)
      (gamma.plan : Measure (E × E)) := by
  obtain ⟨C, _hC, hGrowth⟩ :=
    admissibleConcaveProfileLinearGrowth hProfile
  have hDistance :=
    distanceIntegrableOfMarginalFirstMoments hMu hNu gamma
  have hDominating :
      Integrable (fun z : E × E => C * (1 + ‖z.1 - z.2‖))
        (gamma.plan : Measure (E × E)) :=
    ((integrable_const 1).add hDistance).const_mul C
  refine hDominating.mono' ?_ (ae_of_all _ fun z => ?_)
  · have hMeasurable :
        Measurable (fun z : E × E => profile ‖z.1 - z.2‖) :=
      (concaveProfileDistanceLowerSemicontinuous hProfile.1).measurable
    exact hMeasurable.aestronglyMeasurable
  · simpa only [Real.norm_eq_abs] using
      hGrowth (norm_nonneg (z.1 - z.2))

end ConcaveOTLimit

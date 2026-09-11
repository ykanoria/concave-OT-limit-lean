import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileLinearGrowth
import Theorems.Thm_ConcaveOTLimit_concaveProfileDistanceLowerSemicontinuous
import Theorems.Thm_ConcaveOTLimit_distanceIntegrableOfMarginalFirstMoments

open MeasureTheory

open ConcaveOTLimit

theorem solution
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
  rcases admissibleConcaveProfileLinearGrowth hProfile with
    ⟨C, _hC, hLinearGrowth⟩
  have hDistanceIntegrable :
      Integrable (fun z : E × E => ‖z.1 - z.2‖)
        (gamma.plan : Measure (E × E)) :=
    distanceIntegrableOfMarginalFirstMoments hMu hNu gamma
  refine
    (((integrable_const 1).add hDistanceIntegrable).const_mul C).mono'
      ?_ (ae_of_all _ fun z => ?_)
  · have hMeasurable :
        Measurable (fun z : E × E => profile ‖z.1 - z.2‖) :=
      (concaveProfileDistanceLowerSemicontinuous hProfile.1).measurable
    exact hMeasurable.aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact hLinearGrowth (norm_nonneg (z.1 - z.2))

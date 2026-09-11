import Theorems.Thm_ConcaveOTLimit_isDistanceOptimalIffDistanceCostEqMinimal
import Theorems.Thm_ConcaveOTLimit_powerDifferenceQuotientCostTendstoOfOrliczBound
import Theorems.Thm_ConcaveOTLimit_powerDifferenceQuotientOrliczBound
import Theorems.Thm_ConcaveOTLimit_recoveryBoundIntegrableOfMarginalLogMoments
import Theorems.Thm_ConcaveOTLimit_rescaledPowerProfileCostDecomposition

open Filter MeasureTheory Topology

namespace ConcaveOTLimit

/-- On the distance-optimal face, the rescaled power cost converges along the
constant coupling to logarithmic profile cost. -/
theorem rescaledPowerProfileCostTendstoOfDistanceOptimal
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => Psi ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => Psi ‖y‖) (nu : Measure E))
    (epsilon : Nat -> Real)
    (hEpsilonPos : ∀ n, 0 < epsilon n)
    (hEpsilonLeHalf : ∀ n, epsilon n <= 1 / 2)
    (hEpsilonTendsto : Tendsto epsilon atTop (nhds 0))
    (gamma : FiniteCoupling mu nu)
    (hOptimal : IsDistanceOptimal gamma) :
    Tendsto
      (fun n => rescaledProfileCost powerProfile (epsilon n) gamma)
      atTop
      (nhds (profileCost logarithmicProfile gamma)) := by
  have hDistanceEq :
      distanceCost gamma = minimalDistanceCost mu nu :=
    (isDistanceOptimal_iff_distanceCost_eq_minimal gamma).mp hOptimal
  have hPointwise :
      ∀ n,
        rescaledProfileCost powerProfile (epsilon n) gamma =
          integral (gamma.plan : Measure (E × E))
            (fun z =>
              (powerProfile (epsilon n) ‖z.1 - z.2‖ -
                ‖z.1 - z.2‖) / epsilon n) := by
    intro n
    rw [rescaledPowerProfileCostDecomposition
      hMu hNu gamma (hEpsilonPos n) (hEpsilonLeHalf n), hDistanceEq,
      sub_self, zero_div, zero_add]
  have hQuotientTendsto :=
    powerDifferenceQuotientCostTendstoOfOrliczBound
      (gamma.plan : Measure (E × E))
      (fun z : E × E => ‖z.1 - z.2‖)
      ((measurable_fst.sub measurable_snd).norm)
      (fun z => norm_nonneg (z.1 - z.2))
      epsilon hEpsilonPos hEpsilonLeHalf hEpsilonTendsto
      (fun hPos hHalf hNonnegative =>
        powerDifferenceQuotientOrliczBound hPos hHalf hNonnegative)
      (recoveryBoundIntegrableOfMarginalLogMoments hMu hNu gamma)
  simpa only [hPointwise, profileCost] using hQuotientTendsto

end ConcaveOTLimit

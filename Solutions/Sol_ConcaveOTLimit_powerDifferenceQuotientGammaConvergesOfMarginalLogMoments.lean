import Theorems.Thm_ConcaveOTLimit_logarithmicProfileCostSequentiallyLowerSemicontinuous
import Theorems.Thm_ConcaveOTLimit_powerGammaConvergesOfMarginalLogMoments

open Filter MeasureTheory Topology

open ConcaveOTLimit

theorem solution
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => Psi ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => Psi ‖y‖) (nu : Measure E))
    (epsilon : Nat -> Real)
    (hEpsilonPos : ∀ n, 0 < epsilon n)
    (hEpsilonLeHalf : ∀ n, epsilon n <= 1 / 2)
    (hEpsilonTendsto : Tendsto epsilon atTop (nhds 0)) :
    SequentialGammaConverges
      (fun n (gamma : FiniteCoupling mu nu) =>
        ((integral (gamma.plan : Measure (E × E))
          (fun z =>
            (powerProfile (epsilon n) ‖z.1 - z.2‖ -
              ‖z.1 - z.2‖) / epsilon n) : Real) : EReal))
      (fun gamma : FiniteCoupling mu nu =>
        (profileCost logarithmicProfile gamma : EReal)) := by
  exact powerGammaConvergesOfMarginalLogMoments
    hMu hNu epsilon hEpsilonPos hEpsilonLeHalf hEpsilonTendsto
    (fun hGamma r hr =>
      logarithmicProfileCostSequentiallyLowerSemicontinuous
        hMu hNu hGamma r hr)

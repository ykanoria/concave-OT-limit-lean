import Theorems.Thm_ConcaveOTLimit_powerProfileCostDecomposition
import Theorems.Thm_ConcaveOTLimit_sequentialGammaOfVanishingUniformPerturbation

open Filter MeasureTheory Topology

open ConcaveOTLimit

theorem solution
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (epsilon : Nat -> Real)
    (hEpsilonPos : ∀ n, 0 < epsilon n)
    (hEpsilonTendsto : Tendsto epsilon atTop (nhds 0))
    (bound : Real) (hBoundNonnegative : 0 <= bound)
    (hDistanceIntegrable :
      ∀ gamma : FiniteCoupling mu nu,
        Integrable (fun z : E × E => ‖z.1 - z.2‖)
          (gamma.plan : Measure (E × E)))
    (hQuotientIntegrable :
      ∀ n (gamma : FiniteCoupling mu nu),
        Integrable
          (fun z : E × E =>
            (powerProfile (epsilon n) ‖z.1 - z.2‖ -
              ‖z.1 - z.2‖) / epsilon n)
          (gamma.plan : Measure (E × E)))
    (hQuotientBound :
      ∀ n (gamma : FiniteCoupling mu nu),
        abs
          (integral (gamma.plan : Measure (E × E))
            (fun z =>
              (powerProfile (epsilon n) ‖z.1 - z.2‖ -
                ‖z.1 - z.2‖) / epsilon n) : Real) <= bound)
    (hDistanceSequentiallyContinuous :
      ∀ {gammaSeq : Nat -> FiniteCoupling mu nu}
        {gamma : FiniteCoupling mu nu},
        Tendsto gammaSeq atTop (nhds gamma) ->
          Tendsto (fun n => distanceCost (gammaSeq n))
            atTop (nhds (distanceCost gamma))) :
    SequentialGammaConverges
      (fun n (gamma : FiniteCoupling mu nu) =>
        (profileCost (powerProfile (epsilon n)) gamma : EReal))
      (fun gamma : FiniteCoupling mu nu =>
        (distanceCost gamma : EReal)) := by
  let quotient : Nat -> FiniteCoupling mu nu -> Real :=
    fun n gamma =>
      integral (gamma.plan : Measure (E × E))
        (fun z =>
          (powerProfile (epsilon n) ‖z.1 - z.2‖ -
            ‖z.1 - z.2‖) / epsilon n)
  have hGamma :=
    sequentialGammaOfVanishingUniformPerturbation
      (distanceCost : FiniteCoupling mu nu -> Real)
      quotient epsilon bound hBoundNonnegative hEpsilonTendsto
      (fun n gamma => by
        simpa [quotient] using hQuotientBound n gamma)
      hDistanceSequentiallyContinuous
  have hApproximation :
      (fun n (gamma : FiniteCoupling mu nu) =>
        (profileCost (powerProfile (epsilon n)) gamma : EReal)) =
      (fun n gamma =>
        ((distanceCost gamma + epsilon n * quotient n gamma : Real) :
          EReal)) := by
    funext n gamma
    apply congrArg
    simpa [quotient] using
      powerProfileCostDecomposition gamma
        (hEpsilonPos n).ne'
        (hDistanceIntegrable gamma)
        (hQuotientIntegrable n gamma)
  rw [hApproximation]
  exact hGamma

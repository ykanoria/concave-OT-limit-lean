import Theorems.Thm_ConcaveOTLimit_isDistanceOptimalIffDistanceCostEqMinimal
import Theorems.Thm_ConcaveOTLimit_logarithmicCostIntegrableOfMarginalLogMoments
import Theorems.Thm_ConcaveOTLimit_logarithmicProfileCostLePowerDifferenceQuotientCost
import Theorems.Thm_ConcaveOTLimit_logarithmicProfileCostSequentiallyLowerSemicontinuous
import Theorems.Thm_ConcaveOTLimit_powerQuotientCostIntegrableOfMarginalLogMoments
import Theorems.Thm_ConcaveOTLimit_realSequentialGammaOfLiminfAndConstantRecovery
import Theorems.Thm_ConcaveOTLimit_rescaledPowerProfileCostDecomposition
import Theorems.Thm_ConcaveOTLimit_rescaledPowerProfileCostTendstoOfDistanceOptimal

open Filter MeasureTheory Set Topology

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
    SequentialGammaConvergesOn
      (fun n (gamma : FiniteCoupling mu nu) =>
        (rescaledProfileCost powerProfile (epsilon n) gamma : EReal))
      (fun gamma : FiniteCoupling mu nu =>
        (profileCost logarithmicProfile gamma : EReal))
      (distanceOptimalFace mu nu) := by
  apply realSequentialGammaOfLiminfAndConstantRecovery
    (fun n (gamma : FiniteCoupling mu nu) =>
      rescaledProfileCost powerProfile (epsilon n) gamma)
    (fun gamma : FiniteCoupling mu nu =>
      profileCost logarithmicProfile gamma)
    (distanceOptimalFace mu nu)
  · intro gammaSeq gamma subseq hSubseq hGamma hOptimal r hr
    change IsDistanceOptimal gamma at hOptimal
    have hOptimal' := hOptimal
    change
      IsMinimizerOn Set.univ
        (distanceCost : FiniteCoupling mu nu -> Real) gamma at hOptimal'
    have hDistanceEq :
        distanceCost gamma = minimalDistanceCost mu nu :=
      (isDistanceOptimal_iff_distanceCost_eq_minimal gamma).mp hOptimal
    have hLogEventually :=
      logarithmicProfileCostSequentiallyLowerSemicontinuous
        hMu hNu hGamma r hr
    filter_upwards [hLogEventually] with k hk
    have hLogIntegrable :=
      logarithmicCostIntegrableOfMarginalLogMoments
        hMu hNu (gammaSeq k)
    have hQuotientIntegrable :=
      powerQuotientCostIntegrableOfMarginalLogMoments
        hMu hNu (gammaSeq k)
          (hEpsilonPos (subseq k)) (hEpsilonLeHalf (subseq k))
    have hLogLeQuotient :=
      logarithmicProfileCostLePowerDifferenceQuotientCost
        (gammaSeq k)
        (hEpsilonPos (subseq k))
        (lt_of_le_of_lt (hEpsilonLeHalf (subseq k)) (by norm_num))
        hLogIntegrable hQuotientIntegrable
    have hGapNonnegative :
        0 <=
          (distanceCost (gammaSeq k) - minimalDistanceCost mu nu) /
            epsilon (subseq k) := by
      apply div_nonneg
      · rw [← hDistanceEq]
        exact sub_nonneg.mpr
          (hOptimal'.2 (gammaSeq k) (mem_univ (gammaSeq k)))
      · exact (hEpsilonPos (subseq k)).le
    rw [rescaledPowerProfileCostDecomposition
      hMu hNu (gammaSeq k)
        (hEpsilonPos (subseq k)) (hEpsilonLeHalf (subseq k))]
    exact hk.trans (hLogLeQuotient.trans
      (le_add_of_nonneg_left hGapNonnegative))
  · intro gamma hOptimal
    change IsDistanceOptimal gamma at hOptimal
    exact rescaledPowerProfileCostTendstoOfDistanceOptimal
      hMu hNu epsilon hEpsilonPos hEpsilonLeHalf hEpsilonTendsto
      gamma hOptimal

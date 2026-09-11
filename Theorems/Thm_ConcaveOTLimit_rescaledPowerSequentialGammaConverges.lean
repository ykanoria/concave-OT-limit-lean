import Theorems.Thm_ConcaveOTLimit_distanceCostSequentiallyContinuousOfMarginalLogMoments
import Theorems.Thm_ConcaveOTLimit_isDistanceOptimalIffDistanceCostEqMinimal
import Theorems.Thm_ConcaveOTLimit_powerDifferenceQuotientIntegralLeMarginals
import Theorems.Thm_ConcaveOTLimit_rescaledPowerProfileCostDecomposition
import Theorems.Thm_ConcaveOTLimit_rescaledPowerProfileCostTendstoOfDistanceOptimal
import Theorems.Thm_ConcaveOTLimit_rescaledPowerProfileCostTendstoTopOfNotDistanceOptimal
import Theorems.Thm_ConcaveOTLimit_rescaledPowerSequentialGammaConvergesOnDistanceOptimalFace
import Theorems.Thm_ConcaveOTLimit_sequentialGammaOfLiminfAndConstantRecovery
import Mathlib.Tactic

open Filter MeasureTheory Set Topology

namespace ConcaveOTLimit

/-- Rescaled power costs Gamma-converge globally to logarithmic cost on the
distance-optimal face and positive infinity off that face. -/
theorem rescaledPowerSequentialGammaConverges
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
        (rescaledProfileCost powerProfile (epsilon n) gamma : EReal))
      (fun gamma : FiniteCoupling mu nu =>
        extendedSecondaryCost logarithmicProfile gamma) := by
  let bound : Real :=
    2 * (mu : Measure E).real Set.univ +
      (integral (mu : Measure E) (fun x => Psi (2 * ‖x‖)) : Real) +
      (integral (nu : Measure E) (fun y => Psi (2 * ‖y‖)) : Real)
  have hDistanceNonnegative :
      ∀ eta : FiniteCoupling mu nu, 0 <= distanceCost eta := by
    intro eta
    unfold distanceCost profileCost
    exact integral_nonneg fun z => norm_nonneg (z.1 - z.2)
  have hRangeBounded :
      BddBelow
        (Set.range
          (distanceCost : FiniteCoupling mu nu -> Real)) := by
    refine ⟨0, ?_⟩
    rintro value ⟨eta, rfl⟩
    exact hDistanceNonnegative eta
  have hFaceGamma :=
    rescaledPowerSequentialGammaConvergesOnDistanceOptimalFace
      hMu hNu epsilon hEpsilonPos hEpsilonLeHalf hEpsilonTendsto
  apply sequentialGammaOfLiminfAndConstantRecovery
    (fun n (gamma : FiniteCoupling mu nu) =>
      (rescaledProfileCost powerProfile (epsilon n) gamma : EReal))
    (fun gamma : FiniteCoupling mu nu =>
      extendedSecondaryCost logarithmicProfile gamma)
    Set.univ
  · intro gammaSeq gamma subseq hSubseq hGamma _hDomain r hr
    by_cases hOptimal : IsDistanceOptimal gamma
    · have hr' :
          (r : EReal) < (profileCost logarithmicProfile gamma : EReal) := by
        simpa [extendedSecondaryCost, hOptimal] using hr
      exact hFaceGamma.liminf
        hSubseq hGamma hOptimal r hr'
    · have hMinimalLe :
          minimalDistanceCost mu nu <= distanceCost gamma := by
        unfold minimalDistanceCost
        exact csInf_le hRangeBounded ⟨gamma, rfl⟩
      have hDistanceNe :
          distanceCost gamma ≠ minimalDistanceCost mu nu := by
        exact fun h =>
          hOptimal
            ((isDistanceOptimal_iff_distanceCost_eq_minimal gamma).mpr h)
      let gap : Real :=
        distanceCost gamma - minimalDistanceCost mu nu
      have hGapPos : 0 < gap := by
        dsimp [gap]
        exact sub_pos.mpr
          (lt_of_le_of_ne hMinimalLe hDistanceNe.symm)
      let halfGap : Real := gap / 2
      have hHalfGapPos : 0 < halfGap := by
        dsimp [halfGap]
        positivity
      have hDistanceTendsto :=
        distanceCostSequentiallyContinuousOfMarginalLogMoments
          hMu hNu hGamma
      have hGapEventually :
          ∀ᶠ n in atTop,
            halfGap <=
              distanceCost (gammaSeq n) - minimalDistanceCost mu nu := by
        have hThreshold :
            minimalDistanceCost mu nu + halfGap < distanceCost gamma := by
          dsimp [halfGap, gap]
          linarith
        filter_upwards
          [hDistanceTendsto.eventually_const_lt hThreshold] with n hn
        linarith
      have hEpsilonSubTendsto :
          Tendsto (fun n => epsilon (subseq n)) atTop (nhds 0) :=
        hEpsilonTendsto.comp hSubseq.tendsto_atTop
      have hEpsilonSubRight :
          Tendsto (fun n => epsilon (subseq n))
            atTop (nhdsWithin 0 (Ioi 0)) :=
        tendsto_nhdsWithin_iff.mpr
          ⟨hEpsilonSubTendsto,
            Eventually.of_forall fun n => hEpsilonPos (subseq n)⟩
      have hInverse :
          Tendsto (fun n => (epsilon (subseq n))⁻¹) atTop atTop :=
        hEpsilonSubRight.inv_tendsto_nhdsGT_zero
      have hHalfGapDiv :
          Tendsto (fun n => halfGap / epsilon (subseq n))
            atTop atTop := by
        simpa only [div_eq_mul_inv] using
          tendsto_const_nhds.pos_mul_atTop hHalfGapPos hInverse
      have hLowerEventually :
          ∀ᶠ n in atTop,
            r <= halfGap / epsilon (subseq n) - bound := by
        rw [tendsto_atTop] at hHalfGapDiv
        filter_upwards
          [hHalfGapDiv (r + bound)] with n hn
        linarith
      filter_upwards
        [hGapEventually, hLowerEventually] with n hGapLower hLower
      have hQuotientBound :=
        powerDifferenceQuotientIntegralLeMarginals
          hMu hNu (gammaSeq n)
            (hEpsilonPos (subseq n))
            (hEpsilonLeHalf (subseq n))
      have hQuotientLower :
          -bound <=
            integral ((gammaSeq n).plan : Measure (E × E))
              (fun z =>
                (powerProfile (epsilon (subseq n)) ‖z.1 - z.2‖ -
                  ‖z.1 - z.2‖) / epsilon (subseq n)) := by
        apply neg_le_of_abs_le
        simpa only [bound] using hQuotientBound
      have hGapDivLower :
          halfGap / epsilon (subseq n) <=
            (distanceCost (gammaSeq n) - minimalDistanceCost mu nu) /
              epsilon (subseq n) :=
        (div_le_div_iff_of_pos_right
          (hEpsilonPos (subseq n))).2 hGapLower
      rw [rescaledPowerProfileCostDecomposition
        hMu hNu (gammaSeq n)
          (hEpsilonPos (subseq n))
          (hEpsilonLeHalf (subseq n))]
      exact EReal.coe_le_coe_iff.mpr (by linarith)
  · intro gamma _hDomain
    by_cases hOptimal : IsDistanceOptimal gamma
    · have hReal :=
        rescaledPowerProfileCostTendstoOfDistanceOptimal
          hMu hNu epsilon hEpsilonPos hEpsilonLeHalf hEpsilonTendsto
          gamma hOptimal
      have hCoe :
          Tendsto
            (fun n =>
              (rescaledProfileCost powerProfile (epsilon n) gamma : EReal))
            atTop
            (nhds (profileCost logarithmicProfile gamma : EReal)) :=
        EReal.tendsto_coe.mpr hReal
      simpa [extendedSecondaryCost, hOptimal] using hCoe
    · simpa [extendedSecondaryCost, hOptimal] using
        rescaledPowerProfileCostTendstoTopOfNotDistanceOptimal
          hMu hNu epsilon hEpsilonPos hEpsilonLeHalf hEpsilonTendsto
          gamma hOptimal

end ConcaveOTLimit

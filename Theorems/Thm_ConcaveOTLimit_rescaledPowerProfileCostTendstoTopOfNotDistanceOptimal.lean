import Theorems.Thm_ConcaveOTLimit_isDistanceOptimalIffDistanceCostEqMinimal
import Theorems.Thm_ConcaveOTLimit_powerDifferenceQuotientIntegralLeMarginals
import Theorems.Thm_ConcaveOTLimit_rescaledPowerProfileCostDecomposition
import Mathlib.Tactic

open Filter MeasureTheory Set Topology

namespace ConcaveOTLimit

/-- Away from the distance-optimal face, the rescaled power cost tends to
positive infinity. -/
theorem rescaledPowerProfileCostTendstoTopOfNotDistanceOptimal
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
    (hNotOptimal : ¬ IsDistanceOptimal gamma) :
    Tendsto
      (fun n =>
        (rescaledProfileCost powerProfile (epsilon n) gamma : EReal))
      atTop (nhds ⊤) := by
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
  have hMinimalLe :
      minimalDistanceCost mu nu <= distanceCost gamma := by
    unfold minimalDistanceCost
    exact csInf_le hRangeBounded ⟨gamma, rfl⟩
  have hDistanceNe :
      distanceCost gamma ≠ minimalDistanceCost mu nu := by
    exact fun h =>
      hNotOptimal
        ((isDistanceOptimal_iff_distanceCost_eq_minimal gamma).mpr h)
  let gap : Real :=
    distanceCost gamma - minimalDistanceCost mu nu
  have hGapPos : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr
      (lt_of_le_of_ne hMinimalLe hDistanceNe.symm)
  have hEpsilonRight :
      Tendsto epsilon atTop (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hEpsilonTendsto,
        Eventually.of_forall fun n => hEpsilonPos n⟩
  have hInverse :
      Tendsto (fun n => (epsilon n)⁻¹) atTop atTop :=
    hEpsilonRight.inv_tendsto_nhdsGT_zero
  have hGapDiv :
      Tendsto (fun n => gap / epsilon n) atTop atTop := by
    simpa only [div_eq_mul_inv] using
      tendsto_const_nhds.pos_mul_atTop hGapPos hInverse
  have hGapDivSub :
      Tendsto (fun n => gap / epsilon n - bound) atTop atTop := by
    rw [tendsto_atTop]
    intro r
    filter_upwards [hGapDiv.eventually_ge_atTop (r + bound)] with n hn
    linarith
  have hLower :
      ∀ n,
        gap / epsilon n - bound <=
          rescaledProfileCost powerProfile (epsilon n) gamma := by
    intro n
    have hQuotientBound :=
      powerDifferenceQuotientIntegralLeMarginals
        hMu hNu gamma (hEpsilonPos n) (hEpsilonLeHalf n)
    have hQuotientLower :
        -bound <=
          integral (gamma.plan : Measure (E × E))
            (fun z =>
              (powerProfile (epsilon n) ‖z.1 - z.2‖ -
                ‖z.1 - z.2‖) / epsilon n) := by
      apply neg_le_of_abs_le
      simpa only [bound] using hQuotientBound
    rw [rescaledPowerProfileCostDecomposition
      hMu hNu gamma (hEpsilonPos n) (hEpsilonLeHalf n)]
    dsimp [gap]
    linarith
  apply EReal.tendsto_coe_nhds_top_iff.mpr
  exact tendsto_atTop_mono hLower hGapDivSub

end ConcaveOTLimit

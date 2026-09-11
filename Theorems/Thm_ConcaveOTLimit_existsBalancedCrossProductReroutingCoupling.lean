import Theorems.Thm_ConcaveOTLimit_balancedRestrictionRemoval_le
import Theorems.Thm_ConcaveOTLimit_crossProductReroutingMarginals
import Theorems.Thm_ConcaveOTLimit_existsFiniteMeasureRemainderOfLe
import Theorems.Thm_ConcaveOTLimit_finiteMeasureReplacementPreservesMarginals

open MeasureTheory Set

namespace ConcaveOTLimit

/-- Removing a balanced amount from two disjoint blocks and adding the two
crossed products produces another finite coupling with the same marginals. -/
theorem existsBalancedCrossProductReroutingCoupling
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu) {U V : Set (X × Y)}
    (hMeasurable : MeasurableSet U ∧ MeasurableSet V)
    (hDisjoint : Disjoint U V) (c : NNReal)
    (hCoeffU : c * (gamma.plan.restrict U).mass ≤ 1)
    (hCoeffV : c * (gamma.plan.restrict V).mass ≤ 1) :
    let rho := gamma.plan.restrict U
    let sigma := gamma.plan.restrict V
    let removed := c • (sigma.mass • rho + rho.mass • sigma)
    let added := c •
      ((firstMarginal rho).prod (secondMarginal sigma) +
        (firstMarginal sigma).prod (secondMarginal rho))
    ∃ remainder : FiniteMeasure (X × Y),
      ∃ eta : FiniteCoupling mu nu,
        (removed : Measure (X × Y)) ≤
            (gamma.plan : Measure (X × Y)) ∧
          (remainder : Measure (X × Y)) =
            (gamma.plan : Measure (X × Y)) -
              (removed : Measure (X × Y)) ∧
          (remainder : Measure (X × Y)) ≤
            (gamma.plan : Measure (X × Y)) ∧
          remainder + removed = gamma.plan ∧
          eta.plan = remainder + added := by
  dsimp only
  let rho := gamma.plan.restrict U
  let sigma := gamma.plan.restrict V
  let removed := c • (sigma.mass • rho + rho.mass • sigma)
  let added := c •
    ((firstMarginal rho).prod (secondMarginal sigma) +
      (firstMarginal sigma).prod (secondMarginal rho))
  have hRemoved :
      (removed : Measure (X × Y)) ≤
        (gamma.plan : Measure (X × Y)) := by
    dsimp [removed, rho, sigma]
    simpa only [smul_add, smul_smul] using
      balancedRestrictionRemoval_le gamma.plan hMeasurable hDisjoint c
        hCoeffU hCoeffV
  obtain ⟨remainder, hRemainder, hRemainderLe, hDecomposition⟩ :=
    existsFiniteMeasureRemainderOfLe gamma.plan removed hRemoved
  have hCross := crossProductReroutingMarginals rho sigma
  have hFirst : firstMarginal added = firstMarginal removed := by
    dsimp [added, removed]
    simpa only [firstMarginal, FiniteMeasure.map_smul] using
      congrArg (fun tau : FiniteMeasure X => c • tau) hCross.1
  have hSecond : secondMarginal added = secondMarginal removed := by
    dsimp [added, removed]
    simpa only [secondMarginal, FiniteMeasure.map_smul] using
      congrArg (fun tau : FiniteMeasure Y => c • tau) hCross.2
  have hMarginals :=
    finiteMeasureReplacementPreservesMarginals
      remainder removed added gamma.plan hDecomposition hFirst hSecond
  let eta : FiniteCoupling mu nu :=
    ⟨remainder + added,
      hMarginals.1.trans gamma.property.1,
      hMarginals.2.trans gamma.property.2⟩
  refine ⟨remainder, eta, ?_, hRemainder, hRemainderLe,
    hDecomposition, ?_⟩
  · simpa [removed, rho, sigma] using hRemoved
  · rfl

end ConcaveOTLimit

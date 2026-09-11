import Theorems.Thm_ConcaveOTLimit_crossProductReroutingIntegrable
import Theorems.Thm_ConcaveOTLimit_crossProductReroutingIntegralIdentity
import Theorems.Thm_ConcaveOTLimit_existsForwardBalancedCrossProductReroutingCoupling
import Theorems.Thm_ConcaveOTLimit_existsPositiveBalancedSwapCoefficient
import Theorems.Thm_ConcaveOTLimit_existsPositiveDisjointSwapBlocks
import Theorems.Thm_ConcaveOTLimit_integralSwapGapPositive
import Theorems.Thm_ConcaveOTLimit_profileCostReroutingLtOfAddedLtRemoved
import Mathlib.Tactic.Linarith

open MeasureTheory Set

namespace ConcaveOTLimit

/-- A failed tied-secondary swap at two carrier-separated support points
produces a forward coupling with strictly smaller profile cost. -/
theorem existsForwardReroutingOfFailedSwap
    {mu nu : FiniteMeasure Real}
    {gamma : FiniteCoupling mu nu}
    {profile : Real -> Real}
    {A : Set Real}
    {p q : Real × Real}
    (hProfile : AdmissibleStrictlyConcaveProfile profile)
    (hMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hForward : IsForwardPlan gamma)
    (hpSupport :
      p ∈ Measure.support
        (gamma.plan : Measure (Real × Real)))
    (hqSupport :
      q ∈ Measure.support
        (gamma.plan : Measure (Real × Real)))
    (hpCarrier : p ∈ A ×ˢ Aᶜ)
    (hqCarrier : q ∈ A ×ˢ Aᶜ)
    (hpForward : p.1 < p.2)
    (hqForward : q.1 < q.2)
    (hTie :
      dist p.1 p.2 + dist q.1 q.2 =
        dist p.1 q.2 + dist q.1 p.2)
    (hFailure :
      profile (dist p.1 q.2) + profile (dist q.1 p.2) <
        profile (dist p.1 p.2) + profile (dist q.1 q.2)) :
    ∃ eta : FiniteCoupling mu nu,
      IsForwardPlan eta ∧
        profileCost profile eta < profileCost profile gamma := by
  obtain
      ⟨U, V, delta, hUOpen, hUMeasurable, hpU,
        hVOpen, hVMeasurable, hqV, hDisjoint,
        hUPositive, hVPositive, hDelta, hBlock⟩ :=
    existsPositiveDisjointSwapBlocks hProfile hpSupport hqSupport
      hpCarrier hqCarrier hpForward hqForward hTie hFailure
  have hCrossed :
      ∀ᵐ r ∂(gamma.plan.restrict U : Measure (Real × Real)),
        ∀ᵐ s ∂(gamma.plan.restrict V : Measure (Real × Real)),
          r.1 < s.2 ∧ s.1 < r.2 := by
    filter_upwards [ae_restrict_mem hUMeasurable] with r hr
    filter_upwards [ae_restrict_mem hVMeasurable] with s hs
    exact
      ⟨(hBlock r hr s hs).1,
        (hBlock r hr s hs).2.1⟩
  obtain ⟨c, hc, hCoeffU, hCoeffV⟩ :=
    existsPositiveBalancedSwapCoefficient
      (gamma.plan.restrict U).mass
      (gamma.plan.restrict V).mass
  let rho : FiniteMeasure (Real × Real) :=
    gamma.plan.restrict U
  let sigma : FiniteMeasure (Real × Real) :=
    gamma.plan.restrict V
  let direct : FiniteMeasure (Real × Real) :=
    sigma.mass • rho + rho.mass • sigma
  let crossed : FiniteMeasure (Real × Real) :=
    (firstMarginal rho).prod (secondMarginal sigma) +
      (firstMarginal sigma).prod (secondMarginal rho)
  let removed : FiniteMeasure (Real × Real) := c • direct
  let added : FiniteMeasure (Real × Real) := c • crossed
  have hReroute :=
    existsForwardBalancedCrossProductReroutingCoupling gamma
      ⟨hUMeasurable, hVMeasurable⟩ hDisjoint c
      hCoeffU hCoeffV hForward hCrossed
  dsimp only at hReroute
  obtain
      ⟨remainder, eta, hEtaForward, hRemovedLe,
        hRemainderSub, hRemainderLe, hDecomposition,
        hEtaPlan⟩ :=
    hReroute
  change remainder + removed = gamma.plan at hDecomposition
  change eta.plan = remainder + added at hEtaPlan
  have hRhoLe :
      (rho : Measure (Real × Real)) ≤
        (gamma.plan : Measure (Real × Real)) := by
    dsimp only [rho]
    exact Measure.restrict_le_self
  have hSigmaLe :
      (sigma : Measure (Real × Real)) ≤
        (gamma.plan : Measure (Real × Real)) := by
    dsimp only [sigma]
    exact Measure.restrict_le_self
  have hAdmissible : AdmissibleConcaveProfile profile :=
    ⟨hProfile.1.concaveOn, hProfile.2⟩
  obtain
      ⟨hCostMeasurable, hRhoCost, hSigmaCost,
        hFirstCrossed, hSecondCrossed, hGapIntegrable⟩ :=
    crossProductReroutingIntegrable hAdmissible hMu hNu
      rho sigma hRhoLe hSigmaLe
  let gap : ((Real × Real) × (Real × Real)) -> Real :=
    fun rs =>
      profile (dist rs.1.1 rs.1.2) +
          profile (dist rs.2.1 rs.2.2) -
        profile (dist rs.1.1 rs.2.2) -
        profile (dist rs.2.1 rs.1.2)
  have hGapNested :
      ∀ᵐ r ∂(rho : Measure (Real × Real)),
        ∀ᵐ s ∂(sigma : Measure (Real × Real)),
          delta ≤ gap (r, s) := by
    dsimp only [rho, sigma]
    filter_upwards [ae_restrict_mem hUMeasurable] with r hr
    filter_upwards [ae_restrict_mem hVMeasurable] with s hs
    dsimp only [gap]
    linarith [(hBlock r hr s hs).2.2]
  have hFirstDirectMeasurable :
      Measurable
        (fun rs : (Real × Real) × (Real × Real) =>
          profile (dist rs.1.1 rs.1.2)) :=
    hCostMeasurable.comp (by fun_prop)
  have hSecondDirectMeasurable :
      Measurable
        (fun rs : (Real × Real) × (Real × Real) =>
          profile (dist rs.2.1 rs.2.2)) :=
    hCostMeasurable.comp (by fun_prop)
  have hFirstCrossedMeasurable :
      Measurable
        (fun rs : (Real × Real) × (Real × Real) =>
          profile (dist rs.1.1 rs.2.2)) :=
    hCostMeasurable.comp
      (show
        Measurable
          (fun rs : (Real × Real) × (Real × Real) =>
            (rs.1.1, rs.2.2)) by
        fun_prop)
  have hSecondCrossedMeasurable :
      Measurable
        (fun rs : (Real × Real) × (Real × Real) =>
          profile (dist rs.2.1 rs.1.2)) :=
    hCostMeasurable.comp
      (show
        Measurable
          (fun rs : (Real × Real) × (Real × Real) =>
            (rs.2.1, rs.1.2)) by
        fun_prop)
  have hGapMeasurable : Measurable gap := by
    dsimp only [gap]
    exact
      ((hFirstDirectMeasurable.add hSecondDirectMeasurable).sub
        hFirstCrossedMeasurable).sub hSecondCrossedMeasurable
  have hGapAE :
      ∀ᵐ rs ∂((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
        Measure ((Real × Real) × (Real × Real))),
        delta ≤ gap rs := by
    rw [FiniteMeasure.toMeasure_prod]
    exact
      (Measure.ae_prod_iff_ae_ae
        (measurableSet_le measurable_const hGapMeasurable)).2
        hGapNested
  have hRhoPositive : 0 < rho.mass := by
    simpa only [rho] using hUPositive
  have hSigmaPositive : 0 < sigma.mass := by
    simpa only [sigma] using hVPositive
  have hGapIntegralPositive :
      0 <
        ∫ rs, gap rs
          ∂((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real))) :=
    integralSwapGapPositive rho sigma hRhoPositive hSigmaPositive
      hDelta (by simpa only [gap] using hGapIntegrable) hGapAE
  have hIntegralIdentity :
      (∫ z, profile (dist z.1 z.2)
          ∂(direct : Measure (Real × Real))) -
        (∫ z, profile (dist z.1 z.2)
          ∂(crossed : Measure (Real × Real))) =
      ∫ rs, gap rs
        ∂((rho.prod sigma : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))) := by
    simpa only [direct, crossed, gap] using
      crossProductReroutingIntegralIdentity rho sigma profile
        hCostMeasurable hRhoCost hSigmaCost
        hFirstCrossed hSecondCrossed
  have hBaseCheaper :
      (∫ z, profile (dist z.1 z.2)
          ∂(crossed : Measure (Real × Real))) <
        ∫ z, profile (dist z.1 z.2)
          ∂(direct : Measure (Real × Real)) := by
    linarith [hIntegralIdentity, hGapIntegralPositive]
  let cost : Real × Real -> Real :=
    fun z => profile (dist z.1 z.2)
  have hDirectIntegrable :
      Integrable cost (direct : Measure (Real × Real)) := by
    dsimp only [direct]
    rw [FiniteMeasure.toMeasure_add]
    exact
      hRhoCost.smul_measure_nnreal.add_measure
        hSigmaCost.smul_measure_nnreal
  let cross :
      ((Real × Real) × (Real × Real)) -> Real × Real :=
    fun rs => (rs.1.1, rs.2.2)
  have hCrossMeasurable : Measurable cross := by
    dsimp only [cross]
    fun_prop
  have hFirstMap :
      (firstMarginal rho).prod (secondMarginal sigma) =
        (rho.prod sigma).map cross := by
    simpa only [firstMarginal, secondMarginal, cross,
      Prod.map_apply] using
      FiniteMeasure.map_prod_map rho sigma
        measurable_fst measurable_snd
  have hSecondMap :
      (firstMarginal sigma).prod (secondMarginal rho) =
        (sigma.prod rho).map cross := by
    simpa only [firstMarginal, secondMarginal, cross,
      Prod.map_apply] using
      FiniteMeasure.map_prod_map sigma rho
        measurable_fst measurable_snd
  have hFirstMapIntegrable :
      Integrable cost
        (Measure.map cross
          ((rho.prod sigma : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) := by
    apply
      (integrable_map_measure hCostMeasurable.aestronglyMeasurable
        hCrossMeasurable.aemeasurable).2
    simpa only [cost, cross] using hFirstCrossed
  have hSecondProductIntegrable :
      Integrable
        (fun sr : (Real × Real) × (Real × Real) =>
          cost (sr.1.1, sr.2.2))
        ((sigma.prod rho : FiniteMeasure
          ((Real × Real) × (Real × Real))) :
          Measure ((Real × Real) × (Real × Real))) := by
    simpa only [Function.comp_apply, cost] using hSecondCrossed.swap
  have hSecondMapIntegrable :
      Integrable cost
        (Measure.map cross
          ((sigma.prod rho : FiniteMeasure
            ((Real × Real) × (Real × Real))) :
            Measure ((Real × Real) × (Real × Real)))) := by
    apply
      (integrable_map_measure hCostMeasurable.aestronglyMeasurable
        hCrossMeasurable.aemeasurable).2
    simpa only [Function.comp_apply, cross] using
      hSecondProductIntegrable
  have hFirstAddedIntegrable :
      Integrable cost
        (((firstMarginal rho).prod (secondMarginal sigma) :
          FiniteMeasure (Real × Real)) :
          Measure (Real × Real)) := by
    rw [hFirstMap, FiniteMeasure.toMeasure_map]
    exact hFirstMapIntegrable
  have hSecondAddedIntegrable :
      Integrable cost
        (((firstMarginal sigma).prod (secondMarginal rho) :
          FiniteMeasure (Real × Real)) :
          Measure (Real × Real)) := by
    rw [hSecondMap, FiniteMeasure.toMeasure_map]
    exact hSecondMapIntegrable
  have hCrossedIntegrable :
      Integrable cost (crossed : Measure (Real × Real)) := by
    dsimp only [crossed]
    rw [FiniteMeasure.toMeasure_add]
    exact
      hFirstAddedIntegrable.add_measure hSecondAddedIntegrable
  have hRemovedIntegrable :
      Integrable cost (removed : Measure (Real × Real)) := by
    dsimp only [removed]
    rw [FiniteMeasure.toMeasure_smul]
    exact hDirectIntegrable.smul_measure_nnreal
  have hAddedIntegrable :
      Integrable cost (added : Measure (Real × Real)) := by
    dsimp only [added]
    rw [FiniteMeasure.toMeasure_smul]
    exact hCrossedIntegrable.smul_measure_nnreal
  have hGammaIntegrable :
      Integrable cost
        (gamma.plan : Measure (Real × Real)) := by
    dsimp only [cost]
    simpa only [dist_eq_norm] using
      admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
        hAdmissible
        (by simpa only [Real.norm_eq_abs] using hMu)
        (by simpa only [Real.norm_eq_abs] using hNu)
        gamma
  have hRemainderIntegrable :
      Integrable cost
        (remainder : Measure (Real × Real)) :=
    hGammaIntegrable.mono_measure hRemainderLe
  have hScaledCheaper :
      (∫ z, cost z ∂(added : Measure (Real × Real))) <
        ∫ z, cost z ∂(removed : Measure (Real × Real)) := by
    dsimp only [added, removed]
    rw [FiniteMeasure.toMeasure_smul,
      FiniteMeasure.toMeasure_smul,
      integral_smul_nnreal_measure,
      integral_smul_nnreal_measure]
    simpa only [NNReal.smul_def] using
      mul_lt_mul_of_pos_left hBaseCheaper
        (by exact_mod_cast hc : (0 : Real) < c)
  refine ⟨eta, hEtaForward, ?_⟩
  apply profileCostReroutingLtOfAddedLtRemoved
    hDecomposition.symm hEtaPlan
  · simpa only [cost, dist_eq_norm] using hRemainderIntegrable
  · simpa only [cost, dist_eq_norm] using hRemovedIntegrable
  · simpa only [cost, dist_eq_norm] using hAddedIntegrable
  · simpa only [cost, dist_eq_norm] using hScaledCheaper

end ConcaveOTLimit

import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileLinearGrowth
import Theorems.Thm_ConcaveOTLimit_firstOrderLeDifferenceQuotient
import Mathlib.Analysis.Convex.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Filter MeasureTheory Set Topology

namespace ConcaveOTLimit

private theorem perturbationProfileAdmissible
    {family : Real -> Real -> Real} {firstOrder : Real -> Real}
    (hAssumptions : PerturbationAssumptions family firstOrder)
    {epsilon : Real} (hEpsilon : epsilon ∈ epsilonDomain) :
    AdmissibleConcaveProfile (family epsilon) := by
  refine ⟨(hAssumptions.strictlyConcave hEpsilon).concaveOn, 0, le_rfl, ?_⟩
  intro d hd
  simpa using hAssumptions.nonnegative hEpsilon hd

private theorem firstOrderProfileAdmissible
    {family : Real -> Real -> Real} {firstOrder : Real -> Real}
    (hAssumptions : PerturbationAssumptions family firstOrder) :
    AdmissibleConcaveProfile firstOrder :=
  ⟨hAssumptions.firstOrderStrictlyConcave.concaveOn,
    hAssumptions.firstOrderLowerBound⟩

private theorem quotient_le_quotient
    {family : Real -> Real -> Real} {d delta epsilon : Real}
    (hconv : ConvexOn Real epsilonDomain (fun t => family t d))
    (htend : Tendsto (fun t => family t d)
      (nhdsWithin 0 epsilonDomain) (nhds d))
    (hdelta : delta ∈ epsilonDomain)
    (hepsilon : epsilon ∈ epsilonDomain)
    (hde : delta <= epsilon) :
    (family delta d - d) / delta <=
      (family epsilon d - d) / epsilon := by
  let L := nhdsWithin 0 epsilonDomain
  have hL : NeBot L := by
    simpa [L, epsilonDomain] using
      (left_nhdsWithin_Ioo_neBot (show (0 : Real) < 1 by norm_num))
  let left : Real -> Real :=
    fun a => (family delta d - family a d) / (delta - a)
  let right : Real -> Real :=
    fun a => (family epsilon d - family a d) / (epsilon - a)
  have hleft :
      Tendsto left L (nhds ((family delta d - d) / delta)) := by
    have hnum :
        Tendsto (fun a : Real => family delta d - family a d) L
          (nhds (family delta d - d)) :=
      tendsto_const_nhds.sub htend
    have hden :
        Tendsto (fun a : Real => delta - a) L (nhds delta) := by
      have hid : Tendsto (fun a : Real => a) L (nhds 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using
        (tendsto_const_nhds.sub hid :
          Tendsto (fun a : Real => delta - a) L (nhds (delta - 0)))
    have h := hnum.div hden hdelta.1.ne'
    change Tendsto
      ((fun a : Real => family delta d - family a d) /
        fun a : Real => delta - a) L
        (nhds ((family delta d - d) / delta))
    exact h
  have hright :
      Tendsto right L
        (nhds ((family epsilon d - d) / epsilon)) := by
    have hnum :
        Tendsto (fun a : Real => family epsilon d - family a d) L
          (nhds (family epsilon d - d)) :=
      tendsto_const_nhds.sub htend
    have hden :
        Tendsto (fun a : Real => epsilon - a) L (nhds epsilon) := by
      have hid : Tendsto (fun a : Real => a) L (nhds 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using
        (tendsto_const_nhds.sub hid :
          Tendsto (fun a : Real => epsilon - a) L
            (nhds (epsilon - 0)))
    have h := hnum.div hden hepsilon.1.ne'
    change Tendsto
      ((fun a : Real => family epsilon d - family a d) /
        fun a : Real => epsilon - a) L
        (nhds ((family epsilon d - d) / epsilon))
    exact h
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds hdelta.1),
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds hepsilon.1)] with a ha hadelta haepsilon
  exact hconv.secant_mono ha hdelta hepsilon
    (ne_of_gt hadelta) (ne_of_gt haepsilon) hde

/-- Every perturbation difference quotient is integrable on a coupling
whose fixed marginals have finite first moments. -/
theorem perturbationDifferenceQuotientIntegrableOfMarginalFirstMoments
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    {family : Real -> Real -> Real} {firstOrder : Real -> Real}
    (hAssumptions : PerturbationAssumptions family firstOrder)
    (hMu : Integrable (fun x : E => ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => ‖y‖) (nu : Measure E))
    (gamma : FiniteCoupling mu nu)
    {epsilon : Real} (hEpsilon : epsilon ∈ epsilonDomain) :
    Integrable
      (fun z : E × E =>
        (family epsilon ‖z.1 - z.2‖ - ‖z.1 - z.2‖) / epsilon)
      (gamma.plan : Measure (E × E)) := by
  have hFamily :=
    admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
      (perturbationProfileAdmissible hAssumptions hEpsilon) hMu hNu gamma
  have hDistance :=
    distanceIntegrableOfMarginalFirstMoments hMu hNu gamma
  exact (hFamily.sub hDistance).div_const epsilon

/-- On a fixed coupling with integrable marginal norms, the integrated
perturbation difference quotient converges to the first-order profile
cost. -/
theorem perturbationDifferenceQuotientCostTendstoOfMarginalFirstMoments
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    {family : Real -> Real -> Real} {firstOrder : Real -> Real}
    (hAssumptions : PerturbationAssumptions family firstOrder)
    (hMu : Integrable (fun x : E => ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => ‖y‖) (nu : Measure E))
    (gamma : FiniteCoupling mu nu)
    (epsilon : Nat -> Real)
    (hEpsilon : ∀ n, epsilon n ∈ epsilonDomain)
    (hEpsilonTendsto :
      Tendsto epsilon atTop (nhdsWithin 0 epsilonDomain)) :
    Tendsto
      (fun n =>
        ∫ z,
          (family (epsilon n) ‖z.1 - z.2‖ - ‖z.1 - z.2‖) /
            epsilon n
          ∂(gamma.plan : Measure (E × E)))
      atTop (nhds (profileCost firstOrder gamma)) := by
  let D : E × E -> Real := fun z => ‖z.1 - z.2‖
  have hFirstOrder :
      AdmissibleConcaveProfile firstOrder :=
    firstOrderProfileAdmissible hAssumptions
  obtain ⟨C, hC, hFirstOrderGrowth⟩ :=
    admissibleConcaveProfileLinearGrowth hFirstOrder
  let bound : E × E -> Real :=
    fun z => (C + 4) * (1 + D z)
  have hDistance :
      Integrable D (gamma.plan : Measure (E × E)) :=
    distanceIntegrableOfMarginalFirstMoments hMu hNu gamma
  have hBound :
      Integrable bound (gamma.plan : Measure (E × E)) := by
    exact ((integrable_const 1).add hDistance).const_mul (C + 4)
  have hEpsilonReal :
      Tendsto epsilon atTop (nhds 0) :=
    hEpsilonTendsto.mono_right nhdsWithin_le_nhds
  have hEventuallyHalf : ∀ᶠ n in atTop, epsilon n <= 1 / 2 := by
    exact hEpsilonReal.eventually (Iic_mem_nhds (by norm_num))
  apply tendsto_integral_filter_of_dominated_convergence bound
  · exact Eventually.of_forall fun n =>
      (perturbationDifferenceQuotientIntegrableOfMarginalFirstMoments
        hAssumptions hMu hNu gamma (hEpsilon n)).aestronglyMeasurable
  · filter_upwards [hEventuallyHalf] with n hn
    exact ae_of_all _ fun z => by
      let d := D z
      have hd : 0 <= d := norm_nonneg _
      have hLowerQuotient :
          firstOrder d <=
            (family (epsilon n) d - d) / epsilon n :=
        firstOrderLeDifferenceQuotient hAssumptions (hEpsilon n) hd
      have hFirstOrderLower :
          -(C * (1 + d)) <= firstOrder d :=
        (abs_le.mp (hFirstOrderGrowth hd)).1
      have hHalf : (1 / 2 : Real) ∈ epsilonDomain := by
        constructor <;> norm_num
      have hUpperQuotient :
          (family (epsilon n) d - d) / epsilon n <=
            (family (1 / 2) d - d) / (1 / 2) :=
        quotient_le_quotient
          (hAssumptions.convexInEpsilon hd)
          (hAssumptions.tendsToIdentity hd)
          (hEpsilon n) hHalf hn
      have hHalfGrowth := hAssumptions.growth hHalf hd
      have hHalfUpper :
          (family (1 / 2) d - d) / (1 / 2) <= 4 * (1 + d) := by
        norm_num [div_eq_mul_inv]
        linarith
      rw [Real.norm_eq_abs]
      apply (abs_le).2
      constructor
      · have hOne : 0 <= 1 + d := by linarith
        have hFour : 0 <= 4 * (1 + d) := mul_nonneg (by norm_num) hOne
        linarith
      · have hOne : 0 <= 1 + d := by linarith
        have hCScale : 0 <= C * (1 + d) := mul_nonneg hC hOne
        linarith
  · exact hBound
  · filter_upwards [] with z
    simpa [D] using
      (hAssumptions.firstOrderLimit (norm_nonneg (z.1 - z.2))).comp
        hEpsilonTendsto

end ConcaveOTLimit

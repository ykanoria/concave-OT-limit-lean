import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileCostSequentiallyLowerSemicontinuousOfMarginalFirstMoments
import Theorems.Thm_ConcaveOTLimit_perturbationDifferenceQuotientCostTendstoOfMarginalFirstMoments
import Mathlib.Tactic.Linarith

open Filter MeasureTheory Set Topology

namespace ConcaveOTLimit

/-- Paper Proposition 1: every sequential weak limit of exact optimizers for
an admissible concave perturbation family minimizes the first-order profile
over the distance-optimal face. -/
theorem concaveGammaSelection
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (family : Real -> Real -> Real)
    (firstOrder : Real -> Real)
    (hFamily : PerturbationAssumptions family firstOrder)
    (optimizers : OptimizerFamily mu nu family)
    (eps : Nat -> Real)
    (hEps : ∀ k, eps k ∈ epsilonDomain)
    (hEpsZero :
      Tendsto eps atTop (nhdsWithin 0 epsilonDomain))
    (gammaZero : FiniteCoupling mu nu)
    (hLimit :
      Tendsto (fun k => optimizers.plan (eps k))
        atTop (nhds gammaZero)) :
    IsSecondaryMinimizer firstOrder gammaZero := by
  let quotientProfile : Nat -> Real -> Real :=
    fun k d => (family (eps k) d - d) / eps k
  have hFirstOrderAdmissible :
      AdmissibleConcaveProfile firstOrder :=
    ⟨hFamily.firstOrderStrictlyConcave.concaveOn,
      hFamily.firstOrderLowerBound⟩
  have hDistanceIntegrable :
      ∀ eta : FiniteCoupling mu nu,
        Integrable (fun z : Euclidean n × Euclidean n => ‖z.1 - z.2‖)
          (eta.plan : Measure (Euclidean n × Euclidean n)) := by
    intro eta
    exact distanceIntegrableOfMarginalFirstMoments
      hMarginals.sourceFirstMoment hMarginals.targetFirstMoment eta
  have hFirstOrderIntegrable :
      ∀ eta : FiniteCoupling mu nu,
        Integrable
          (fun z : Euclidean n × Euclidean n =>
            firstOrder ‖z.1 - z.2‖)
          (eta.plan : Measure (Euclidean n × Euclidean n)) := by
    intro eta
    exact admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
      hFirstOrderAdmissible hMarginals.sourceFirstMoment
        hMarginals.targetFirstMoment eta
  have hPerturbationAdmissible :
      ∀ k, AdmissibleConcaveProfile (family (eps k)) := by
    intro k
    refine
      ⟨(hFamily.strictlyConcave (hEps k)).concaveOn,
        0, le_rfl, ?_⟩
    intro d hd
    simpa using hFamily.nonnegative (hEps k) hd
  have hPerturbationIntegrable :
      ∀ k (eta : FiniteCoupling mu nu),
        Integrable
          (fun z : Euclidean n × Euclidean n =>
            family (eps k) ‖z.1 - z.2‖)
          (eta.plan : Measure (Euclidean n × Euclidean n)) := by
    intro k eta
    exact admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
      (hPerturbationAdmissible k) hMarginals.sourceFirstMoment
        hMarginals.targetFirstMoment eta
  have hQuotientIntegrable :
      ∀ k (eta : FiniteCoupling mu nu),
        Integrable
          (fun z : Euclidean n × Euclidean n =>
            quotientProfile k ‖z.1 - z.2‖)
          (eta.plan : Measure (Euclidean n × Euclidean n)) := by
    intro k eta
    exact
      perturbationDifferenceQuotientIntegrableOfMarginalFirstMoments
        hFamily hMarginals.sourceFirstMoment hMarginals.targetFirstMoment
        eta (hEps k)
  have hCostDecomposition :
      ∀ k (eta : FiniteCoupling mu nu),
        profileCost (family (eps k)) eta =
          distanceCost eta +
            eps k * profileCost (quotientProfile k) eta := by
    intro k eta
    change
      (∫ z, family (eps k) ‖z.1 - z.2‖
          ∂(eta.plan : Measure (Euclidean n × Euclidean n))) =
        (∫ z, ‖z.1 - z.2‖
          ∂(eta.plan : Measure (Euclidean n × Euclidean n))) +
        eps k *
          ∫ z, quotientProfile k ‖z.1 - z.2‖
            ∂(eta.plan : Measure (Euclidean n × Euclidean n))
    rw [← integral_const_mul,
      ← integral_add (hDistanceIntegrable eta)
        ((hQuotientIntegrable k eta).const_mul (eps k))]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [quotientProfile]
    field_simp [(hEps k).1.ne']
    <;> ring
  have hFirstOrderLeQuotient :
      ∀ k (eta : FiniteCoupling mu nu),
        profileCost firstOrder eta <=
          profileCost (quotientProfile k) eta := by
    intro k eta
    unfold profileCost
    exact integral_mono (hFirstOrderIntegrable eta)
      (hQuotientIntegrable k eta) fun z =>
        firstOrderLeDifferenceQuotient
          hFamily (hEps k) (norm_nonneg (z.1 - z.2))
  have hQuotientTendsto :
      ∀ eta : FiniteCoupling mu nu,
        Tendsto (fun k => profileCost (quotientProfile k) eta)
          atTop (nhds (profileCost firstOrder eta)) := by
    intro eta
    simpa [quotientProfile, profileCost] using
      perturbationDifferenceQuotientCostTendstoOfMarginalFirstMoments
        hFamily hMarginals.sourceFirstMoment hMarginals.targetFirstMoment
        eta eps hEps hEpsZero
  have hEpsReal : Tendsto eps atTop (nhds 0) :=
    hEpsZero.mono_right nhdsWithin_le_nhds
  have hFixedPerturbationTendsto :
      ∀ eta : FiniteCoupling mu nu,
        Tendsto (fun k => profileCost (family (eps k)) eta)
          atTop (nhds (distanceCost eta)) := by
    intro eta
    have hRight :
        Tendsto
          (fun k =>
            distanceCost eta +
              eps k * profileCost (quotientProfile k) eta)
          atTop (nhds (distanceCost eta)) := by
      convert tendsto_const_nhds.add
        (hEpsReal.mul (hQuotientTendsto eta)) using 1 <;> simp
    exact hRight.congr' (Eventually.of_forall fun k =>
      (hCostDecomposition k eta).symm)
  have hDistanceTendsto :
      Tendsto
        (fun k => distanceCost (optimizers.plan (eps k)))
        atTop (nhds (distanceCost gammaZero)) :=
    distanceCostSequentiallyContinuousOfMarginalFirstMoments
      hMarginals.sourceFirstMoment hMarginals.targetFirstMoment hLimit
  have hFirstOrderLowerSemicontinuous :
      ∀ r < profileCost firstOrder gammaZero,
        ∀ᶠ k in atTop,
          r <= profileCost firstOrder (optimizers.plan (eps k)) :=
    admissibleConcaveProfileCostSequentiallyLowerSemicontinuousOfMarginalFirstMoments
      hFirstOrderAdmissible hMarginals.sourceFirstMoment
        hMarginals.targetFirstMoment hMarginals.positiveMass hLimit
  have hEventuallyFirstOrderLower :
      ∀ᶠ k in atTop,
        profileCost firstOrder gammaZero - 1 <=
          profileCost firstOrder (optimizers.plan (eps k)) :=
    hFirstOrderLowerSemicontinuous
      (profileCost firstOrder gammaZero - 1) (by linarith)

  have hDistanceOptimal : IsDistanceOptimal gammaZero := by
    change
      IsMinimizerOn Set.univ
        (distanceCost : FiniteCoupling mu nu -> Real) gammaZero
    refine ⟨mem_univ gammaZero, ?_⟩
    intro eta _hEta
    have hLowerTendsto :
        Tendsto
          (fun k =>
            distanceCost (optimizers.plan (eps k)) +
              eps k * (profileCost firstOrder gammaZero - 1))
          atTop (nhds (distanceCost gammaZero)) := by
      convert hDistanceTendsto.add
        (hEpsReal.mul_const (profileCost firstOrder gammaZero - 1))
        using 1 <;> simp
    have hEventuallyComparison :
        ∀ᶠ k in atTop,
          distanceCost (optimizers.plan (eps k)) +
              eps k * (profileCost firstOrder gammaZero - 1) <=
            profileCost (family (eps k)) eta := by
      filter_upwards [hEventuallyFirstOrderLower] with k hk
      have hQuotientLower :
          profileCost firstOrder gammaZero - 1 <=
            profileCost (quotientProfile k)
              (optimizers.plan (eps k)) :=
        hk.trans
          (hFirstOrderLeQuotient k (optimizers.plan (eps k)))
      calc
        distanceCost (optimizers.plan (eps k)) +
              eps k * (profileCost firstOrder gammaZero - 1) <=
            distanceCost (optimizers.plan (eps k)) +
              eps k * profileCost (quotientProfile k)
                (optimizers.plan (eps k)) :=
          add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left hQuotientLower (hEps k).1.le)
        _ = profileCost (family (eps k))
              (optimizers.plan (eps k)) :=
          (hCostDecomposition k (optimizers.plan (eps k))).symm
        _ <= profileCost (family (eps k)) eta :=
          (optimizers.uniquelyOptimal (eps k) (hEps k)).1.2
            eta (mem_univ eta)
    exact le_of_tendsto_of_tendsto hLowerTendsto
      (hFixedPerturbationTendsto eta) hEventuallyComparison

  change
    IsMinimizerOn (distanceOptimalFace mu nu)
      (profileCost firstOrder) gammaZero
  refine ⟨hDistanceOptimal, ?_⟩
  intro eta hEtaDistanceOptimal
  have hQuotientComparison :
      ∀ k,
        profileCost (quotientProfile k) (optimizers.plan (eps k)) <=
          profileCost (quotientProfile k) eta := by
    intro k
    have hPerturbationComparison :
        profileCost (family (eps k)) (optimizers.plan (eps k)) <=
          profileCost (family (eps k)) eta :=
      (optimizers.uniquelyOptimal (eps k) (hEps k)).1.2
        eta (mem_univ eta)
    have hDistanceComparison :
        distanceCost eta <= distanceCost (optimizers.plan (eps k)) :=
      hEtaDistanceOptimal.2
        (optimizers.plan (eps k)) (mem_univ _)
    rw [hCostDecomposition k (optimizers.plan (eps k)),
      hCostDecomposition k eta] at hPerturbationComparison
    have hScaled :
        eps k *
            profileCost (quotientProfile k) (optimizers.plan (eps k)) <=
          eps k * profileCost (quotientProfile k) eta := by
      linarith
    exact le_of_mul_le_mul_left hScaled (hEps k).1
  by_contra hNot
  have hStrict :
      profileCost firstOrder eta < profileCost firstOrder gammaZero :=
    lt_of_not_ge hNot
  let r : Real :=
    (profileCost firstOrder eta + profileCost firstOrder gammaZero) / 2
  have hEtaLt : profileCost firstOrder eta < r := by
    dsimp [r]
    linarith
  have hRLt : r < profileCost firstOrder gammaZero := by
    dsimp [r]
    linarith
  have hLower := hFirstOrderLowerSemicontinuous r hRLt
  have hUpper :=
    (hQuotientTendsto eta).eventually_lt_const hEtaLt
  have hFalse : ∀ᶠ k in (atTop : Filter Nat), False := by
    filter_upwards [hLower, hUpper] with k hkLower hkUpper
    have hMiddle :
        profileCost firstOrder (optimizers.plan (eps k)) <=
          profileCost (quotientProfile k) eta :=
      (hFirstOrderLeQuotient k (optimizers.plan (eps k))).trans
        (hQuotientComparison k)
    exact (not_lt_of_ge (hkLower.trans hMiddle)) hkUpper
  have hExists : ∃ k : Nat, False := Filter.Eventually.exists hFalse
  exact hExists.elim fun _ hk => hk

end ConcaveOTLimit

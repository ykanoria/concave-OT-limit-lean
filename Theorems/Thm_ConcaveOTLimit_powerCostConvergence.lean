import Theorems.Thm_ConcaveOTLimit_finiteCouplingIsCompact
import Theorems.Thm_ConcaveOTLimit_finiteGraphPlanTendstoInMeasureOfMeasurable
import Theorems.Thm_ConcaveOTLimit_logarithmicSecondaryUniqueness
import Theorems.Thm_ConcaveOTLimit_powerGammaSelection
import Theorems.Thm_ConcaveOTLimit_powerMinimizerGraphness
import Theorems.Thm_ConcaveOTLimit_strictConcaveRadialOptimizerProducer
import Theorems.Thm_ConcaveOTLimit_tendstoOfSeqCompactUniqueSubseqLimit
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

open Filter MeasureTheory Set Topology

namespace ConcaveOTLimit

/-- Conditional assembly of `powerCostConvergence` from exactly the two
existence inputs not supplied by the convergence modules: a graph-plan unique
logarithmic secondary minimizer and a family of exact power optimizers. -/
theorem powerCostConvergence_of_producers
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu)
    (hLogarithmic :
      exists gammaSharp : FiniteCoupling mu nu,
        exists tSharp : Euclidean n -> Euclidean n,
          IsGraphPlan gammaSharp tSharp /\
            IsUniqueSecondaryMinimizer
              logarithmicProfile gammaSharp)
    (hPowerOptimizers :
      Nonempty (OptimizerFamily mu nu powerProfile)) :
    exists gammaSharp : FiniteCoupling mu nu,
      exists tSharp : Euclidean n -> Euclidean n,
        exists optimizers : OptimizerFamily mu nu powerProfile,
          IsGraphPlan gammaSharp tSharp /\
            IsUniqueSecondaryMinimizer
              logarithmicProfile gammaSharp /\
            Tendsto optimizers.plan
              (nhdsWithin 0 epsilonDomain) (nhds gammaSharp) /\
            TendstoInMeasure
              (mu : Measure (Euclidean n))
              optimizers.transportMap
              (nhdsWithin 0 epsilonDomain) tSharp := by
  classical
  rcases hLogarithmic with
    ⟨gammaSharp, tSharp, hGraphSharp, hUniqueSharp⟩
  rcases hPowerOptimizers with ⟨optimizers⟩

  have hFirstMarginalMass
      {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
      (rho : FiniteMeasure (X × Y)) :
      (firstMarginal rho).mass = rho.mass := by
    simp [firstMarginal, FiniteMeasure.mass,
      FiniteMeasure.map_apply _ measurable_fst MeasurableSet.univ]
  have hPlanMass (gamma : FiniteCoupling mu nu) :
      gamma.plan.mass = mu.mass := by
    calc
      gamma.plan.mass = (firstMarginal gamma.plan).mass :=
        (hFirstMarginalMass gamma.plan).symm
      _ = mu.mass :=
        congrArg (fun rho : FiniteMeasure (Euclidean n) => rho.mass)
          gamma.property.1
  have hPlanNonzero (gamma : FiniteCoupling mu nu) :
      gamma.plan ≠ 0 :=
    gamma.plan.mass_nonzero_iff.mp (by
      rw [hPlanMass gamma]
      exact ne_of_gt hPower.positiveMass)

  let normalizedPlan :
      FiniteCoupling mu nu ->
        ProbabilityMeasure (Euclidean n × Euclidean n) :=
    fun gamma => gamma.plan.normalize
  have hNormalizedPlanContinuous : Continuous normalizedPlan := by
    rw [continuous_iff_continuousAt]
    intro gamma
    simpa [normalizedPlan] using
      FiniteMeasure.tendsto_normalize_of_tendsto
        (by
          simpa [FiniteCoupling.plan] using
            (continuous_subtype_val.tendsto gamma))
        (hPlanNonzero gamma)

  let reconstructPlan :
      ProbabilityMeasure (Euclidean n × Euclidean n) ->
        FiniteMeasure (Euclidean n × Euclidean n) :=
    fun rho => mu.mass • rho.toFiniteMeasure
  have hReconstructPlanContinuous : Continuous reconstructPlan := by
    exact (continuous_const_smul mu.mass).comp
      ProbabilityMeasure.toFiniteMeasure_continuous
  have hReconstructPlan (gamma : FiniteCoupling mu nu) :
      reconstructPlan (normalizedPlan gamma) = gamma.plan := by
    dsimp [reconstructPlan, normalizedPlan]
    rw [← hPlanMass gamma]
    exact gamma.plan.self_eq_mass_smul_normalize.symm
  have hNormalizedPlanInducing : IsInducing normalizedPlan := by
    apply IsInducing.of_comp
      hNormalizedPlanContinuous hReconstructPlanContinuous
    have hComposition :
        reconstructPlan ∘ normalizedPlan =
          (fun gamma : FiniteCoupling mu nu => gamma.plan) := by
      funext gamma
      exact hReconstructPlan gamma
    rw [hComposition]
    simpa [FiniteCoupling.plan] using
      (IsEmbedding.subtypeVal :
        IsEmbedding
          (Subtype.val :
            FiniteCoupling mu nu ->
              FiniteMeasure (Euclidean n × Euclidean n))).isInducing

  letI : TopologicalSpace.PseudoMetrizableSpace
      (FiniteCoupling mu nu) :=
    hNormalizedPlanInducing.pseudoMetrizableSpace
  letI : CompactSpace (FiniteCoupling mu nu) :=
    isCompact_univ_iff.mp (finiteCouplingIsCompact mu nu)
  letI : SeqCompactSpace (FiniteCoupling mu nu) :=
    compactSpace_iff_seqCompactSpace.mp inferInstance

  have hPlanConvergence :
      Tendsto optimizers.plan
        (nhdsWithin 0 epsilonDomain) (nhds gammaSharp) := by
    rw [Filter.tendsto_iff_seq_tendsto]
    intro epsilon hEpsilonZero
    have hEventuallyDomain :
        ∀ᶠ k in atTop, epsilon k ∈ epsilonDomain :=
      eventually_mem_of_tendsto_nhdsWithin hEpsilonZero
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hEventuallyDomain
    let shiftedEpsilon : Nat -> Real :=
      fun k => epsilon (k + N)
    have hShiftedDomain :
        ∀ k, shiftedEpsilon k ∈ epsilonDomain := by
      intro k
      exact hN (k + N) (Nat.le_add_left N k)
    have hShiftedZero :
        Tendsto shiftedEpsilon atTop
          (nhdsWithin 0 epsilonDomain) := by
      simpa [shiftedEpsilon] using
        hEpsilonZero.comp (Filter.tendsto_add_atTop_nat N)
    have hShiftedPlan :
        Tendsto (fun k => optimizers.plan (shiftedEpsilon k))
          atTop (nhds gammaSharp) := by
      apply tendstoOfSeqCompactUniqueSubseqLimit
      intro phi hPhi gamma hGamma
      have hSubsequenceZero :
          Tendsto (fun k => shiftedEpsilon (phi k)) atTop
            (nhdsWithin 0 epsilonDomain) :=
        hShiftedZero.comp hPhi.tendsto_atTop
      have hSecondary :
          IsSecondaryMinimizer logarithmicProfile gamma :=
        (powerGammaSelection n mu nu hPower optimizers
          (fun k => shiftedEpsilon (phi k))
          (fun k => hShiftedDomain (phi k))
          hSubsequenceZero gamma (by
            simpa using hGamma)).2.2.2.2
      exact hUniqueSharp.2 gamma hSecondary
    have hShiftedOriginal :
        Tendsto
          (fun k => optimizers.plan (epsilon (k + N)))
          atTop (nhds gammaSharp) := by
      simpa [shiftedEpsilon] using hShiftedPlan
    have hOriginal :
        Tendsto (fun k => optimizers.plan (epsilon k))
          atTop (nhds gammaSharp) :=
      (Filter.tendsto_add_atTop_iff_nat N).mp hShiftedOriginal
    simpa [Function.comp_def] using hOriginal

  obtain ⟨hTSharp, hGammaSharpPlan⟩ := hGraphSharp
  let measurableMap : Real -> Euclidean n -> Euclidean n :=
    fun epsilon =>
      if hEpsilon : epsilon ∈ epsilonDomain then
        optimizers.transportMap epsilon
      else
        tSharp
  have hMeasurableMap :
      ∀ epsilon, Measurable (measurableMap epsilon) := by
    intro epsilon
    by_cases hEpsilon : epsilon ∈ epsilonDomain
    · simpa [measurableMap, hEpsilon] using
        (optimizers.graph epsilon hEpsilon).choose
    · simpa [measurableMap, hEpsilon] using hTSharp
  have hUnderlyingPlanConvergence :
      Tendsto (fun epsilon => (optimizers.plan epsilon).plan)
        (nhdsWithin 0 epsilonDomain) (nhds gammaSharp.plan) := by
    simpa [FiniteCoupling.plan] using
      (continuous_subtype_val.tendsto gammaSharp).comp
        hPlanConvergence
  have hGraphPlansEventually :
      (fun epsilon =>
        (optimizers.plan epsilon).plan) =ᶠ[
          nhdsWithin 0 epsilonDomain]
      (fun epsilon =>
        finiteGraphPlan mu (measurableMap epsilon)
          (hMeasurableMap epsilon)) := by
    filter_upwards [eventually_mem_nhdsWithin] with epsilon hEpsilon
    obtain ⟨hMap, hPlan⟩ := optimizers.graph epsilon hEpsilon
    simpa [measurableMap, hEpsilon] using hPlan
  have hGraphPlanConvergence :
      Tendsto
        (fun epsilon =>
          finiteGraphPlan mu (measurableMap epsilon)
            (hMeasurableMap epsilon))
        (nhdsWithin 0 epsilonDomain)
        (nhds (finiteGraphPlan mu tSharp hTSharp)) := by
    rw [← hGammaSharpPlan]
    exact Tendsto.congr' hGraphPlansEventually
      hUnderlyingPlanConvergence
  have hMeasurableMapConvergence :
      TendstoInMeasure
        (mu : Measure (Euclidean n))
        measurableMap
        (nhdsWithin 0 epsilonDomain) tSharp :=
    finiteGraphPlanTendstoInMeasureOfMeasurable
      mu measurableMap tSharp hMeasurableMap hTSharp
        hGraphPlanConvergence
  have hMapsEventually :
      ∀ᶠ epsilon in nhdsWithin 0 epsilonDomain,
        measurableMap epsilon = optimizers.transportMap epsilon := by
    filter_upwards [eventually_mem_nhdsWithin] with epsilon hEpsilon
    simp [measurableMap, hEpsilon]
  have hMapConvergence :
      TendstoInMeasure
        (mu : Measure (Euclidean n))
        optimizers.transportMap
        (nhdsWithin 0 epsilonDomain) tSharp := by
    exact TendstoInMeasure.congr'
      (hMapsEventually.mono fun _ hMaps =>
        Filter.Eventually.of_forall fun x => congrFun hMaps x)
      Filter.EventuallyEq.rfl hMeasurableMapConvergence

  exact
    ⟨gammaSharp, tSharp, optimizers, ⟨hTSharp, hGammaSharpPlan⟩,
      hUniqueSharp,
      hPlanConvergence, hMapConvergence⟩

/-- The exact mathematical boundary after power-minimizer existence,
integrability, uniqueness, and family choice have been discharged. -/
theorem powerCostConvergence_of_logarithmic_and_power_graph_minimizers
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu)
    (hLogarithmic :
      exists gammaSharp : FiniteCoupling mu nu,
        exists tSharp : Euclidean n -> Euclidean n,
          IsGraphPlan gammaSharp tSharp /\
            IsUniqueSecondaryMinimizer
              logarithmicProfile gammaSharp)
    (hGraph :
      forall epsilon, epsilon ∈ epsilonDomain ->
        forall gamma : FiniteCoupling mu nu,
          IsProfileMinimizer (powerProfile epsilon) gamma ->
            exists T : Euclidean n -> Euclidean n,
              IsGraphPlan gamma T) :
    exists gammaSharp : FiniteCoupling mu nu,
      exists tSharp : Euclidean n -> Euclidean n,
        exists optimizers : OptimizerFamily mu nu powerProfile,
          IsGraphPlan gammaSharp tSharp /\
            IsUniqueSecondaryMinimizer
              logarithmicProfile gammaSharp /\
            Tendsto optimizers.plan
              (nhdsWithin 0 epsilonDomain) (nhds gammaSharp) /\
            TendstoInMeasure
              (mu : Measure (Euclidean n))
              optimizers.transportMap
              (nhdsWithin 0 epsilonDomain) tSharp := by
  exact powerCostConvergence_of_producers
    n mu nu hPower hLogarithmic
      (nonempty_powerOptimizerFamily_of_graph_minimizers
        n mu nu hPower hGraph)

/-- The two residual producers are also necessary for the exact convergence
conclusion, so this characterizes the remaining proof boundary. -/
theorem powerCostConvergence_result_iff_producers
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu) :
    (exists gammaSharp : FiniteCoupling mu nu,
      exists tSharp : Euclidean n -> Euclidean n,
        exists optimizers : OptimizerFamily mu nu powerProfile,
          IsGraphPlan gammaSharp tSharp /\
            IsUniqueSecondaryMinimizer
              logarithmicProfile gammaSharp /\
            Tendsto optimizers.plan
              (nhdsWithin 0 epsilonDomain) (nhds gammaSharp) /\
            TendstoInMeasure
              (mu : Measure (Euclidean n))
              optimizers.transportMap
              (nhdsWithin 0 epsilonDomain) tSharp) ↔
      ((exists gammaSharp : FiniteCoupling mu nu,
        exists tSharp : Euclidean n -> Euclidean n,
          IsGraphPlan gammaSharp tSharp /\
            IsUniqueSecondaryMinimizer
              logarithmicProfile gammaSharp) /\
        (forall epsilon, epsilon ∈ epsilonDomain ->
          forall gamma : FiniteCoupling mu nu,
            IsProfileMinimizer (powerProfile epsilon) gamma ->
              exists T : Euclidean n -> Euclidean n,
                IsGraphPlan gamma T)) := by
  constructor
  · rintro
      ⟨gammaSharp, tSharp, optimizers, hGraphSharp, hUniqueSharp,
        _hPlanConvergence, _hMapConvergence⟩
    refine
      ⟨⟨gammaSharp, tSharp, hGraphSharp, hUniqueSharp⟩, ?_⟩
    intro epsilon hEpsilon gamma hGamma
    have hGammaEq :
        gamma = optimizers.plan epsilon :=
      (optimizers.uniquelyOptimal epsilon hEpsilon).2 gamma hGamma
    subst gamma
    exact
      ⟨optimizers.transportMap epsilon,
        optimizers.graph epsilon hEpsilon⟩
  · rintro ⟨hLogarithmic, hGraph⟩
    exact
      powerCostConvergence_of_logarithmic_and_power_graph_minimizers
        n mu nu hPower hLogarithmic hGraph

/-- Paper Theorem 10: exact power-cost optimizers converge weakly, and their
inducing maps converge in source measure, to the unique logarithmic
secondary minimizer. -/
theorem powerCostConvergence
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu) :
    exists gammaSharp : FiniteCoupling mu nu,
      exists tSharp : Euclidean n -> Euclidean n,
        exists optimizers : OptimizerFamily mu nu powerProfile,
          IsGraphPlan gammaSharp tSharp /\
            IsUniqueSecondaryMinimizer
              logarithmicProfile gammaSharp /\
            Tendsto optimizers.plan
              (nhdsWithin 0 epsilonDomain) (nhds gammaSharp) /\
            TendstoInMeasure
              (mu : Measure (Euclidean n))
              optimizers.transportMap
              (nhdsWithin 0 epsilonDomain) tSharp := by
  apply powerCostConvergence_of_producers n mu nu hPower
  · obtain
      ⟨gammaSharp, tSharp, hGraphSharp, _hIntrinsicSharp,
        hUniqueSharp⟩ :=
      logarithmicSecondaryUniqueness n mu nu hPower
    exact ⟨gammaSharp, tSharp, hGraphSharp, hUniqueSharp⟩
  · exact nonempty_powerOptimizerFamily n mu nu hPower

#print axioms powerCostConvergence

end ConcaveOTLimit

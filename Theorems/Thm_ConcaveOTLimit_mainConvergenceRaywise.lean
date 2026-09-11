import Definitions.Def_LiteralJuilletExcursion
import Theorems.Thm_ConcaveOTLimit_literalJuilletPairingConstruction
import Theorems.Thm_ConcaveOTLimit_mainConvergenceAssembly
import Theorems.Thm_ConcaveOTLimit_oneDimensionalExcursionVariational
import Theorems.Thm_ConcaveOTLimit_perturbationMinimizerGraphness
import Theorems.Thm_ConcaveOTLimit_strictConcaveRadialOptimizerProducer
import Theorems.Thm_ConcaveOTLimit_uniqueSecondaryMinimizer

open Filter MeasureTheory Topology

namespace ConcaveOTLimit

/-- Constructing one literal coupling suffices for full one-dimensional
identification, by direct uniqueness of laminar couplings. -/
theorem literalJuilletIdentification_of_construction
    (hConstruction : LiteralJuilletConstructionPremise) :
    LiteralJuilletIdentificationPremise := by
  intro mu nu gamma hAtomless hSingular hDominates hCoupling
    _hForward hExcursion
  have hMass : mu.mass = nu.mass := by
    have hFirstMass :
        (firstMarginal gamma).mass = gamma.mass := by
      change (gamma.map Prod.fst) Set.univ = gamma Set.univ
      rw [FiniteMeasure.map_apply gamma measurable_fst MeasurableSet.univ]
      rfl
    have hSecondMass :
        (secondMarginal gamma).mass = gamma.mass := by
      change (gamma.map Prod.snd) Set.univ = gamma Set.univ
      rw [FiniteMeasure.map_apply gamma measurable_snd MeasurableSet.univ]
      rfl
    calc
      mu.mass = (firstMarginal gamma).mass :=
        congrArg (fun eta : FiniteMeasure Real => eta.mass)
          hCoupling.1.symm
      _ = gamma.mass := hFirstMass
      _ = (secondMarginal gamma).mass := hSecondMass.symm
      _ = nu.mass :=
        congrArg (fun eta : FiniteMeasure Real => eta.mass)
          hCoupling.2
  obtain ⟨eta, hEtaLiteral, hEtaExcursion⟩ :=
    hConstruction mu nu hMass hAtomless hSingular hDominates
  let gammaCoupling : FiniteCoupling mu nu := ⟨gamma, hCoupling⟩
  let etaCoupling : FiniteCoupling mu nu := ⟨eta, hEtaLiteral.1⟩
  have hCouplingsEqual : gammaCoupling = etaCoupling :=
    monotoneArchPlan_unique hAtomless hDominates
      gammaCoupling etaCoupling hExcursion hEtaExcursion
  have hMeasuresEqual : gamma = eta :=
    congrArg Subtype.val hCouplingsEqual
  obtain ⟨_hEtaCoupling, data, hEtaData⟩ := hEtaLiteral
  refine ⟨hCoupling, data, ?_⟩
  calc
    (gamma : Measure (Real × Real)) =
        (eta : Measure (Real × Real)) := by
      rw [hMeasuresEqual]
    _ = literalJuilletExcursionMeasure data := hEtaData

/-- The single one-dimensional identification premise upgrades every existing
raywise excursion disintegration to a literal completed-graph
disintegration. -/
theorem literalRaywiseExcursionDisintegration_of_identification
    (h1D : LiteralJuilletIdentificationPremise)
    {n : Nat}
    {Gamma : Set (Euclidean n × Euclidean n)}
    {mu nu : FiniteMeasure (Euclidean n)}
    {gamma : FiniteMeasure (Euclidean n × Euclidean n)}
    {transportMap : Euclidean n -> Euclidean n}
    (D : RaywiseExcursionDisintegration
      Gamma mu nu gamma transportMap) :
    Nonempty
      (LiteralRaywiseExcursionDisintegration
        Gamma mu nu gamma transportMap) := by
  refine ⟨{ base := D, componentIsLiteral := ?_ }⟩
  filter_upwards
    [D.coordinateSourceAtomless,
      D.coordinateMarginalsMutuallySingular,
      D.coordinateTargetDominates,
      D.coordinateComponentForward,
      D.componentIsExcursion] with
      R hAtomless hSingular hDominates hForward hExcursion
  have hForwardMapped :
      ∀ᵐ z ∂((D.component R).map (fun z =>
          (rayCoordinate R z.1, rayCoordinate R z.2)) :
        Measure (Real × Real)),
        z.1 <= z.2 := by
    apply
      (ae_map_iff
        ((measurable_rayCoordinate R).prodMap
          (measurable_rayCoordinate R)).aemeasurable
        (measurableSet_le measurable_fst measurable_snd)).2
    exact hForward
  exact h1D
    ((D.source R).map (rayCoordinate R))
    ((D.target R).map (rayCoordinate R))
    ((D.component R).map fun z =>
      (rayCoordinate R z.1, rayCoordinate R z.2))
    hAtomless hSingular hDominates hExcursion.1 hForwardMapped hExcursion

/-- Faithful raywise convergence theorem, conditional on exactly the
one-dimensional identification of variational/laminar plans with Juillet's
literal completed-graph construction. -/
theorem mainConvergenceRaywise_of_literalJuilletIdentification
    (h1D : LiteralJuilletIdentificationPremise)
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu) :
    ∃ gammaSharp : FiniteCoupling mu nu,
      ∃ tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
          IsIntrinsicGeneralizedECPlan mu nu gammaSharp /\
          IsRaywiseGeneralizedECPlan mu nu gammaSharp tSharp /\
          ∀ family : Real -> Real -> Real,
            ∀ firstOrder : Real -> Real,
              PerturbationAssumptions family firstOrder ->
                ∃ optimizers : OptimizerFamily mu nu family,
                  TendstoInMeasure
                    (mu : Measure (Euclidean n))
                    optimizers.transportMap
                    (nhdsWithin 0 epsilonDomain) tSharp := by
  obtain
      ⟨gammaSharp, tSharp, hGraphSharp, hIntrinsicSharp,
        u, hu, Gamma, hGamma, hGammaSigma, hRaywise⟩ :=
    uniqueSecondaryMinimizer n mu nu hMarginals
  refine
    ⟨gammaSharp, tSharp, hGraphSharp, hIntrinsicSharp,
      ⟨u, hu, Gamma, hGamma, hGammaSigma, ?_⟩, ?_⟩
  · exact
      literalRaywiseExcursionDisintegration_of_identification
        h1D hRaywise.some
  · intro family firstOrder hFamily
    obtain ⟨optimizers⟩ :=
      optimizerFamilyProducer_of_perturbation_graph_minimizers
        n mu nu hMarginals
        (perturbationMinimizerGraphPremise n mu nu hMarginals)
        family ⟨firstOrder, hFamily⟩
    refine ⟨optimizers, ?_⟩
    have hFirstOrderAdmissible :
        AdmissibleStrictlyConcaveProfile firstOrder :=
      ⟨hFamily.firstOrderStrictlyConcave,
        hFamily.firstOrderLowerBound⟩
    have hUniqueSharp :
        IsUniqueSecondaryMinimizer firstOrder gammaSharp :=
      hIntrinsicSharp firstOrder hFirstOrderAdmissible
    have hPlanConvergence :
        Tendsto optimizers.plan
          (nhdsWithin 0 epsilonDomain) (nhds gammaSharp) :=
      optimizerPlanConvergence_of_uniqueSecondary
        n mu nu hMarginals gammaSharp family firstOrder hFamily
          optimizers hUniqueSharp
    exact
      optimizerTransportMapConvergence_of_planConvergence
        n mu nu gammaSharp tSharp hGraphSharp family optimizers
          hPlanConvergence

/-- Faithful raywise convergence from the sharper one-dimensional boundary
which asks only for construction of the literal completed-graph coupling. -/
theorem mainConvergenceRaywise_of_literalJuilletConstruction
    (hConstruction : LiteralJuilletConstructionPremise)
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu) :
    ∃ gammaSharp : FiniteCoupling mu nu,
      ∃ tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
          IsIntrinsicGeneralizedECPlan mu nu gammaSharp /\
          IsRaywiseGeneralizedECPlan mu nu gammaSharp tSharp /\
          ∀ family : Real -> Real -> Real,
            ∀ firstOrder : Real -> Real,
              PerturbationAssumptions family firstOrder ->
                ∃ optimizers : OptimizerFamily mu nu family,
                  TendstoInMeasure
                    (mu : Measure (Euclidean n))
                    optimizers.transportMap
                    (nhdsWithin 0 epsilonDomain) tSharp :=
  mainConvergenceRaywise_of_literalJuilletIdentification
    (literalJuilletIdentification_of_construction hConstruction)
      n mu nu hMarginals

/-- Faithful raywise convergence with the remaining one-dimensional input
stated directly as measurable crossing decomposition plus the oriented
occupation identity. -/
theorem mainConvergenceRaywise_of_crossingAnalysis
    (hCrossingAnalysis :
      ∀ (mu nu : FiniteMeasure Real),
        IsAtomlessFinite mu ->
          FiniteMutuallySingular mu nu ->
            StochasticallyDominates nu mu ->
              ∃ _decomposition :
                  MeasurablePositiveCrossingDecomposition mu nu,
                PositiveCrossingIndicatrixIdentity mu nu)
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu) :
    ∃ gammaSharp : FiniteCoupling mu nu,
      ∃ tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
          IsIntrinsicGeneralizedECPlan mu nu gammaSharp /\
          IsRaywiseGeneralizedECPlan mu nu gammaSharp tSharp /\
          ∀ family : Real -> Real -> Real,
            ∀ firstOrder : Real -> Real,
              PerturbationAssumptions family firstOrder ->
                ∃ optimizers : OptimizerFamily mu nu family,
                  TendstoInMeasure
                    (mu : Measure (Euclidean n))
                    optimizers.transportMap
                    (nhdsWithin 0 epsilonDomain) tSharp :=
  mainConvergenceRaywise_of_literalJuilletIdentification
    (literalJuilletIdentificationPremise_of_crossingDecompositions
      hCrossingAnalysis)
    n mu nu hMarginals

/-- Faithful raywise convergence from the sole remaining one-dimensional
analytic input, the oriented positive-crossing indicatrix identity. -/
theorem mainConvergenceRaywise_of_positiveCrossingIndicatrix
    (hIndicatrix :
      ∀ (mu nu : FiniteMeasure Real),
        IsAtomlessFinite mu ->
          FiniteMutuallySingular mu nu ->
            StochasticallyDominates nu mu ->
              PositiveCrossingIndicatrixIdentity mu nu)
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu) :
    ∃ gammaSharp : FiniteCoupling mu nu,
      ∃ tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
          IsIntrinsicGeneralizedECPlan mu nu gammaSharp /\
          IsRaywiseGeneralizedECPlan mu nu gammaSharp tSharp /\
          ∀ family : Real -> Real -> Real,
            ∀ firstOrder : Real -> Real,
              PerturbationAssumptions family firstOrder ->
                ∃ optimizers : OptimizerFamily mu nu family,
                  TendstoInMeasure
                    (mu : Measure (Euclidean n))
                    optimizers.transportMap
                    (nhdsWithin 0 epsilonDomain) tSharp :=
  mainConvergenceRaywise_of_literalJuilletIdentification
    (literalJuilletIdentificationPremise_of_positiveCrossingIndicatrix
      hIndicatrix)
    n mu nu hMarginals

end ConcaveOTLimit

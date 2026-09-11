import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
import Theorems.Thm_ConcaveOTLimit_canonicalRaywiseReplacementIntegration
import Theorems.Thm_ConcaveOTLimit_concaveProfileDistanceLowerSemicontinuous
import Theorems.Thm_ConcaveOTLimit_distanceCostIntegrableOfMarginalLogMoments
import Theorems.Thm_ConcaveOTLimit_finiteCouplingIsCompact
import Theorems.Thm_ConcaveOTLimit_fixedMassPlanNormalization
import Theorems.Thm_ConcaveOTLimit_powerProfileStrictConcave
import Theorems.Thm_ConcaveOTLimit_probabilityLintegralLowerSemicontinuous
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.Tactic.Linarith

open Filter MeasureTheory Set Topology

noncomputable section

namespace ConcaveOTLimit

/-- The profile-level hypotheses in the increasing strictly-concave radial
optimal-transport theorem needed by the optimizer producer. -/
structure StrictConcaveRadialProfileAssumptions
    (profile : Real -> Real) : Prop where
  map_zero : profile 0 = 0
  nonnegative : forall {r : Real}, 0 <= r -> 0 <= profile r
  continuous : Continuous profile
  strictlyIncreasing : StrictMonoOn profile (Ici 0)
  strictlyConcave : StrictConcaveOn Real (Ici 0) profile

/-- Power profiles in the perturbation domain satisfy all elementary
profile hypotheses of the radial graph-optimizer theorem. -/
theorem powerProfile_strictConcaveRadialProfileAssumptions
    {epsilon : Real} (hEpsilon : epsilon ∈ epsilonDomain) :
    StrictConcaveRadialProfileAssumptions (powerProfile epsilon) := by
  have hExponentPos : 0 < 1 - epsilon := by
    linarith [hEpsilon.2]
  refine
    { map_zero := ?_
      nonnegative := ?_
      continuous := ?_
      strictlyIncreasing := ?_
      strictlyConcave := powerProfileStrictConcave hEpsilon }
  · simp [powerProfile, Real.zero_rpow hExponentPos.ne']
  · intro r hr
    exact Real.rpow_nonneg hr _
  · unfold powerProfile
    exact Real.continuous_rpow_const hExponentPos.le
  · unfold powerProfile
    exact Real.strictMonoOn_rpow_Ici_of_exponent_pos hExponentPos

/-- On a regular distance-optimal contact support, every secondary minimizer
of an increasing strictly concave radial profile is the canonical raywise
graph replacement and is therefore the unique secondary minimizer. -/
theorem strictConcaveRadial_secondaryMinimizer_graph_unique_of_regularSupport
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hSigma : IsSigmaCompact Gamma)
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (hCyclic : IsDistanceCyclicallyMonotone.{0, 0} Gamma)
    (hSupportedOptimal :
      ∀ eta : FiniteCoupling mu nu,
        IsDistanceOptimal eta -> IsSupported eta Gamma)
    (hIntegration :
      CanonicalRaywiseReplacementIntegrationPremise
        n mu nu Gamma hRegularity)
    {profile : Real -> Real}
    (hProfile : StrictConcaveRadialProfileAssumptions profile)
    (gamma : FiniteCoupling mu nu)
    (hMin : IsSecondaryMinimizer profile gamma) :
    (∃ T : Euclidean n -> Euclidean n, IsGraphPlan gamma T) /\
      IsUniqueSecondaryMinimizer profile gamma := by
  have hStrict : AdmissibleStrictlyConcaveProfile profile := by
    refine ⟨hProfile.strictlyConcave, 0, le_rfl, ?_⟩
    intro d hd
    simpa using hProfile.nonnegative hd
  have hConcave : AdmissibleConcaveProfile profile :=
    ⟨hStrict.1.concaveOn, hStrict.2⟩
  have hGammaSupported : IsSupported gamma Gamma :=
    hSupportedOptimal gamma hMin.1
  obtain
      ⟨gammaSharp, tSharp, hGraphSharp, hCyclicOptimal, _hSameRay,
        _hDisintegration, hComparison⟩ :=
    canonicalRaywiseReplacement_of_integrationPremise_and_optimalInput
      n mu nu hMarginals Gamma hSigma hDiagonal hRegularity
      gamma hGammaSupported hMin.1 hIntegration
  have hSharpOptimal : IsDistanceOptimal gammaSharp :=
    hCyclicOptimal hCyclic
  have hSharpLeGamma :
      profileCost profile gammaSharp <= profileCost profile gamma :=
    (hComparison gamma hGammaSupported profile hConcave).1
  have hGammaLeSharp :
      profileCost profile gamma <= profileCost profile gammaSharp :=
    hMin.2 gammaSharp hSharpOptimal
  have hGammaEqSharp : gamma = gammaSharp :=
    ((hComparison gamma hGammaSupported profile hConcave).2 hStrict).1
      (le_antisymm hSharpLeGamma hGammaLeSharp)
  constructor
  · exact ⟨tSharp, hGammaEqSharp.symm ▸ hGraphSharp⟩
  · refine ⟨hMin, ?_⟩
    intro eta hEta
    have hEtaSupported : IsSupported eta Gamma :=
      hSupportedOptimal eta hEta.1
    have hSharpLeEta :
        profileCost profile gammaSharp <= profileCost profile eta :=
      (hComparison eta hEtaSupported profile hConcave).1
    have hEtaLeSharp :
        profileCost profile eta <= profileCost profile gammaSharp :=
      hEta.2 gammaSharp hSharpOptimal
    have hEtaEqSharp : eta = gammaSharp :=
      ((hComparison eta hEtaSupported profile hConcave).2 hStrict).1
        (le_antisymm hSharpLeEta hEtaLeSharp)
    exact hEtaEqSharp.trans hGammaEqSharp.symm

/-- Pointwise existence of graph-induced unique minimizers is enough to
construct an optimizer family. Values outside `epsilonDomain` are filled
using the optimizer at `1 / 2`. -/
theorem nonempty_optimizerFamily_of_pointwise_graph_unique
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (mu nu : FiniteMeasure E) (family : Real -> Real -> Real)
    (hPointwise :
      forall epsilon, epsilon ∈ epsilonDomain ->
        exists gamma : FiniteCoupling mu nu,
          exists T : E -> E,
            IsGraphPlan gamma T /\
              IsUniqueProfileMinimizer (family epsilon) gamma) :
    Nonempty (OptimizerFamily mu nu family) := by
  classical
  have hHalf : (1 / 2 : Real) ∈ epsilonDomain := by
    constructor <;> norm_num
  let defaultGamma : FiniteCoupling mu nu :=
    Classical.choose (hPointwise (1 / 2) hHalf)
  let defaultMap : E -> E :=
    Classical.choose
      (Classical.choose_spec (hPointwise (1 / 2) hHalf))
  let plan : Real -> FiniteCoupling mu nu :=
    fun epsilon =>
      if h : epsilon ∈ epsilonDomain then
        Classical.choose (hPointwise epsilon h)
      else
        defaultGamma
  let transportMap : Real -> E -> E :=
    fun epsilon =>
      if h : epsilon ∈ epsilonDomain then
        Classical.choose
          (Classical.choose_spec (hPointwise epsilon h))
      else
        defaultMap
  refine ⟨{
    plan := plan
    transportMap := transportMap
    graph := ?_
    uniquelyOptimal := ?_
  }⟩
  · intro epsilon hEpsilon
    dsimp only [plan, transportMap]
    simp only [hEpsilon, dite_true]
    exact
      (Classical.choose_spec
        (Classical.choose_spec (hPointwise epsilon hEpsilon))).1
  · intro epsilon hEpsilon
    dsimp only [plan]
    simp only [hEpsilon, dite_true]
    exact
      (Classical.choose_spec
        (Classical.choose_spec (hPointwise epsilon hEpsilon))).2

/-- `OptimizerFamily` contains no compatibility condition between distinct
parameters: its nonemptiness is exactly pointwise graph-induced unique
optimality on `epsilonDomain`. -/
theorem nonempty_optimizerFamily_iff_pointwise_graph_unique
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (mu nu : FiniteMeasure E) (family : Real -> Real -> Real) :
    Nonempty (OptimizerFamily mu nu family) ↔
      forall epsilon, epsilon ∈ epsilonDomain ->
        exists gamma : FiniteCoupling mu nu,
          exists T : E -> E,
            IsGraphPlan gamma T /\
              IsUniqueProfileMinimizer (family epsilon) gamma := by
  constructor
  · rintro ⟨optimizers⟩ epsilon hEpsilon
    exact
      ⟨optimizers.plan epsilon, optimizers.transportMap epsilon,
        optimizers.graph epsilon hEpsilon,
        optimizers.uniquelyOptimal epsilon hEpsilon⟩
  · exact nonempty_optimizerFamily_of_pointwise_graph_unique mu nu family

/-- The midpoint of two finite couplings is again a finite coupling with the
same marginals. -/
def midpointFiniteCoupling
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma eta : FiniteCoupling mu nu) : FiniteCoupling mu nu := by
  let half : NNReal := 1 / 2
  have hGammaFirst : gamma.plan.map Prod.fst = mu := by
    simpa [firstMarginal, FiniteCoupling.plan] using gamma.property.1
  have hEtaFirst : eta.plan.map Prod.fst = mu := by
    simpa [firstMarginal, FiniteCoupling.plan] using eta.property.1
  have hGammaSecond : gamma.plan.map Prod.snd = nu := by
    simpa [secondMarginal, FiniteCoupling.plan] using gamma.property.2
  have hEtaSecond : eta.plan.map Prod.snd = nu := by
    simpa [secondMarginal, FiniteCoupling.plan] using eta.property.2
  refine ⟨half • gamma.plan + half • eta.plan, ?_⟩
  constructor
  · change firstMarginal (half • gamma.plan + half • eta.plan) = mu
    simp only [firstMarginal, FiniteMeasure.map_add measurable_fst,
      FiniteMeasure.map_smul, hGammaFirst, hEtaFirst]
    rw [← add_smul]
    norm_num [half]
  · change secondMarginal (half • gamma.plan + half • eta.plan) = nu
    simp only [secondMarginal, FiniteMeasure.map_add measurable_snd,
      FiniteMeasure.map_smul, hGammaSecond, hEtaSecond]
    rw [← add_smul]
    norm_num [half]

/-- Profile cost is affine at the midpoint of two couplings whenever the two
endpoint costs are integrable. -/
theorem profileCost_midpointFiniteCoupling
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    {mu nu : FiniteMeasure E} {profile : Real -> Real}
    (gamma eta : FiniteCoupling mu nu)
    (hGamma :
      Integrable (fun z : E × E => profile ‖z.1 - z.2‖)
        (gamma.plan : Measure (E × E)))
    (hEta :
      Integrable (fun z : E × E => profile ‖z.1 - z.2‖)
        (eta.plan : Measure (E × E))) :
    profileCost profile (midpointFiniteCoupling gamma eta) =
      (1 / 2 : Real) * profileCost profile gamma +
        (1 / 2 : Real) * profileCost profile eta := by
  let cost : E × E -> Real :=
    fun z => profile ‖z.1 - z.2‖
  change
    (∫ z, cost z
      ∂((((1 / 2 : NNReal) • gamma.plan +
          (1 / 2 : NNReal) • eta.plan :
        FiniteMeasure (E × E))) : Measure (E × E))) =
      (1 / 2 : Real) *
          (∫ z, cost z ∂(gamma.plan : Measure (E × E))) +
        (1 / 2 : Real) *
          (∫ z, cost z ∂(eta.plan : Measure (E × E)))
  rw [FiniteMeasure.toMeasure_add, FiniteMeasure.toMeasure_smul,
    FiniteMeasure.toMeasure_smul,
    integral_add_measure hGamma.smul_measure_nnreal
      hEta.smul_measure_nnreal,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  norm_num [NNReal.smul_def, cost]

private theorem leftPlan_absolutelyContinuous_midpoint
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma eta : FiniteCoupling mu nu) :
    (gamma.plan : Measure (X × Y)) ≪
      ((midpointFiniteCoupling gamma eta).plan :
        Measure (X × Y)) := by
  intro s hs
  change
    (((1 / 2 : NNReal) • gamma.plan +
        (1 / 2 : NNReal) • eta.plan :
      FiniteMeasure (X × Y)) : Measure (X × Y)) s = 0 at hs
  simp only [FiniteMeasure.toMeasure_add,
    FiniteMeasure.toMeasure_smul, Measure.coe_add, Pi.add_apply,
    Measure.coe_smul, Pi.smul_apply, add_eq_zero] at hs
  have h := hs.1
  norm_num at h
  exact h

private theorem rightPlan_absolutelyContinuous_midpoint
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma eta : FiniteCoupling mu nu) :
    (eta.plan : Measure (X × Y)) ≪
      ((midpointFiniteCoupling gamma eta).plan :
        Measure (X × Y)) := by
  intro s hs
  change
    (((1 / 2 : NNReal) • gamma.plan +
        (1 / 2 : NNReal) • eta.plan :
      FiniteMeasure (X × Y)) : Measure (X × Y)) s = 0 at hs
  simp only [FiniteMeasure.toMeasure_add,
    FiniteMeasure.toMeasure_smul, Measure.coe_add, Pi.add_apply,
    Measure.coe_smul, Pi.smul_apply, add_eq_zero] at hs
  have h := hs.2
  norm_num at h
  exact h

private theorem ae_target_eq_of_graphPlan
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableEq Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu) (T : X -> Y)
    (hGraph : IsGraphPlan gamma T) :
    ∀ᵐ z ∂(gamma.plan : Measure (X × Y)), z.2 = T z.1 := by
  obtain ⟨hT, hPlan⟩ := hGraph
  rw [hPlan]
  change
    ∀ᵐ z ∂Measure.map (fun x => (x, T x)) (mu : Measure X),
      z.2 = T z.1
  apply
    (ae_map_iff (measurable_id.prodMk hT).aemeasurable
      (measurableSet_eq_fun measurable_snd
        (hT.comp measurable_fst))).2
  exact Eventually.of_forall fun _ => rfl

private theorem graphPlan_of_ae_target_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu) (T : X -> Y)
    (hT : Measurable T)
    (hTarget :
      ∀ᵐ z ∂(gamma.plan : Measure (X × Y)), z.2 = T z.1) :
    IsGraphPlan gamma T := by
  refine ⟨hT, ?_⟩
  apply FiniteMeasure.toMeasure_injective
  simp only [FiniteCoupling.plan, finiteGraphPlan,
    FiniteMeasure.toMeasure_map]
  have hFirst :
      Measure.map Prod.fst (gamma.plan : Measure (X × Y)) =
        (mu : Measure X) := by
    simpa [firstMarginal, FiniteCoupling.plan] using congrArg
      (fun rho : FiniteMeasure X => (rho : Measure X))
      gamma.property.1
  calc
    (gamma.plan : Measure (X × Y)) =
        Measure.map id
          (gamma.plan : Measure (X × Y)) := Measure.map_id.symm
    _ = Measure.map
          ((fun x => (x, T x)) ∘ Prod.fst)
          (gamma.plan : Measure (X × Y)) := by
      apply Measure.map_congr
      filter_upwards [hTarget] with z hz
      exact Prod.ext rfl hz
    _ = Measure.map (fun x => (x, T x))
          (Measure.map Prod.fst
            (gamma.plan : Measure (X × Y))) := by
      exact
        (Measure.map_map
          (measurable_id.prodMk hT) measurable_fst).symm
    _ = Measure.map (fun x => (x, T x))
          (mu : Measure X) := by rw [hFirst]

/-- If profile cost is integrable on every coupling and every minimizer is a
graph plan, then every minimizer is unique. Indeed, the midpoint of two
minimizers is again a minimizer and hence a graph; absolute continuity of
each endpoint with respect to the midpoint puts both endpoints on that same
graph. -/
theorem isUniqueProfileMinimizer_of_all_minimizers_graph
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [MeasurableEq E]
    {mu nu : FiniteMeasure E} {profile : Real -> Real}
    (hIntegrable :
      forall rho : FiniteCoupling mu nu,
        Integrable (fun z : E × E => profile ‖z.1 - z.2‖)
          (rho.plan : Measure (E × E)))
    (hGraph :
      forall rho : FiniteCoupling mu nu,
        IsProfileMinimizer profile rho ->
          exists T : E -> E, IsGraphPlan rho T)
    (gamma : FiniteCoupling mu nu)
    (hGamma : IsProfileMinimizer profile gamma) :
    IsUniqueProfileMinimizer profile gamma := by
  refine ⟨hGamma, ?_⟩
  intro eta hEta
  have hCostsEq :
      profileCost profile gamma = profileCost profile eta :=
    le_antisymm
      (hGamma.2 eta (mem_univ eta))
      (hEta.2 gamma (mem_univ gamma))
  let midpoint := midpointFiniteCoupling gamma eta
  have hMidpointCost :
      profileCost profile midpoint =
        (1 / 2 : Real) * profileCost profile gamma +
          (1 / 2 : Real) * profileCost profile eta := by
    exact profileCost_midpointFiniteCoupling gamma eta
      (hIntegrable gamma) (hIntegrable eta)
  have hMidpoint : IsProfileMinimizer profile midpoint := by
    refine ⟨mem_univ midpoint, ?_⟩
    intro rho hRho
    rw [hMidpointCost, ← hCostsEq]
    nlinarith [hGamma.2 rho hRho]
  obtain ⟨T, hMidpointGraph⟩ := hGraph midpoint hMidpoint
  obtain ⟨hT, hMidpointPlan⟩ := hMidpointGraph
  have hMidpointTarget :=
    ae_target_eq_of_graphPlan midpoint T ⟨hT, hMidpointPlan⟩
  have hGammaTarget :=
    (leftPlan_absolutelyContinuous_midpoint gamma eta).ae_eq
      hMidpointTarget
  have hEtaTarget :=
    (rightPlan_absolutelyContinuous_midpoint gamma eta).ae_eq
      hMidpointTarget
  obtain ⟨_hTGamma, hGammaPlan⟩ :=
    graphPlan_of_ae_target_eq gamma T hT hGammaTarget
  obtain ⟨_hTEta, hEtaPlan⟩ :=
    graphPlan_of_ae_target_eq eta T hT hEtaTarget
  apply Subtype.ext
  change eta.plan = gamma.plan
  rw [hEtaPlan, hGammaPlan]

/-- Minimizer existence, integrability, and graphness of every minimizer
construct an optimizer family. Uniqueness follows from graphness by the
midpoint argument above. -/
theorem nonempty_optimizerFamily_of_minimizers_and_graph
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [MeasurableEq E]
    (mu nu : FiniteMeasure E) (family : Real -> Real -> Real)
    (hExists :
      forall epsilon, epsilon ∈ epsilonDomain ->
        exists gamma : FiniteCoupling mu nu,
          IsProfileMinimizer (family epsilon) gamma)
    (hIntegrable :
      forall epsilon, epsilon ∈ epsilonDomain ->
        forall gamma : FiniteCoupling mu nu,
          Integrable
            (fun z : E × E => family epsilon ‖z.1 - z.2‖)
            (gamma.plan : Measure (E × E)))
    (hGraph :
      forall epsilon, epsilon ∈ epsilonDomain ->
        forall gamma : FiniteCoupling mu nu,
          IsProfileMinimizer (family epsilon) gamma ->
            exists T : E -> E, IsGraphPlan gamma T) :
    Nonempty (OptimizerFamily mu nu family) := by
  apply nonempty_optimizerFamily_of_pointwise_graph_unique
    mu nu family
  intro epsilon hEpsilon
  obtain ⟨gamma, hGamma⟩ := hExists epsilon hEpsilon
  obtain ⟨T, hGraphGamma⟩ :=
    hGraph epsilon hEpsilon gamma hGamma
  refine ⟨gamma, T, hGraphGamma, ?_⟩
  exact
    isUniqueProfileMinimizer_of_all_minimizers_graph
      (hIntegrable epsilon hEpsilon)
      (hGraph epsilon hEpsilon) gamma hGamma

/-- A direct producer interface retaining an explicit uniqueness premise. -/
theorem nonempty_optimizerFamily_of_minimizers_and_graph_unique
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    (mu nu : FiniteMeasure E) (family : Real -> Real -> Real)
    (hExists :
      forall epsilon, epsilon ∈ epsilonDomain ->
        exists gamma : FiniteCoupling mu nu,
          IsProfileMinimizer (family epsilon) gamma)
    (hGraphUnique :
      forall epsilon, epsilon ∈ epsilonDomain ->
        forall gamma : FiniteCoupling mu nu,
          IsProfileMinimizer (family epsilon) gamma ->
            (exists T : E -> E, IsGraphPlan gamma T) /\
              forall eta : FiniteCoupling mu nu,
                IsProfileMinimizer (family epsilon) eta -> eta = gamma) :
    Nonempty (OptimizerFamily mu nu family) := by
  apply nonempty_optimizerFamily_of_pointwise_graph_unique mu nu family
  intro epsilon hEpsilon
  obtain ⟨gamma, hGamma⟩ := hExists epsilon hEpsilon
  obtain ⟨⟨T, hGraph⟩, hUnique⟩ :=
    hGraphUnique epsilon hEpsilon gamma hGamma
  exact ⟨gamma, T, hGraph, hGamma, hUnique⟩

/-- Equal positive finite masses have a coupling, obtained by taking the
source product with the normalized target. -/
theorem nonempty_finiteCoupling_of_equal_positive_mass
    {E : Type*} [MeasurableSpace E] [Nonempty E]
    (mu nu : FiniteMeasure E)
    (hMass : mu.mass = nu.mass) (hPositive : 0 < mu.mass) :
    Nonempty (FiniteCoupling mu nu) := by
  have hNuNonzero : nu ≠ 0 := by
    apply nu.mass_nonzero_iff.mp
    rw [← hMass]
    exact ne_of_gt hPositive
  let gamma : FiniteMeasure (E × E) :=
    mu.prod nu.normalize.toFiniteMeasure
  refine ⟨⟨gamma, ?_⟩⟩
  constructor
  · change firstMarginal gamma = mu
    change
      (mu.prod nu.normalize.toFiniteMeasure).map Prod.fst = mu
    rw [FiniteMeasure.map_fst_prod]
    simp only [ProbabilityMeasure.toFiniteMeasure_apply_eq_apply,
      ProbabilityMeasure.coeFn_univ, one_smul]
  · change secondMarginal gamma = nu
    calc
      secondMarginal gamma =
          mu.mass • nu.normalize.toFiniteMeasure := by
        change
          (mu.prod nu.normalize.toFiniteMeasure).map Prod.snd =
            mu.mass • nu.normalize.toFiniteMeasure
        rw [FiniteMeasure.map_snd_prod]
        rfl
      _ = nu.mass • nu.normalize.toFiniteMeasure := by rw [hMass]
      _ = nu := nu.self_eq_mass_smul_normalize.symm

/-- A nonnegative lower-semicontinuous profile integrand gives a
lower-semicontinuous real-valued profile cost on a positive fixed-mass
coupling space, provided all its costs are integrable. -/
theorem profileCost_lowerSemicontinuous_of_nonnegative
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E} {profile : Real -> Real}
    (hPositive : 0 < mu.mass)
    (hLower :
      LowerSemicontinuous
        (fun z : E × E => profile ‖z.1 - z.2‖))
    (hNonnegative :
      forall {r : Real}, 0 <= r -> 0 <= profile r)
    (hIntegrable :
      forall gamma : FiniteCoupling mu nu,
        Integrable (fun z : E × E => profile ‖z.1 - z.2‖)
          (gamma.plan : Measure (E × E))) :
    LowerSemicontinuous
      (profileCost (mu := mu) (nu := nu) profile) := by
  let cost : E × E -> Real :=
    fun z => profile ‖z.1 - z.2‖
  let normalizedIntegral : FiniteCoupling mu nu -> Real :=
    fun gamma =>
      ∫ z, cost z
        ∂(gamma.plan.normalize : Measure (E × E))
  have hCostNonnegative : 0 <= cost := by
    intro z
    exact hNonnegative (norm_nonneg _)
  have hProbabilityLower :
      LowerSemicontinuous
        (fun P : ProbabilityMeasure (E × E) =>
          ∫⁻ z, ENNReal.ofReal (cost z)
            ∂(P : Measure (E × E))) :=
    probabilityLintegralLowerSemicontinuous
      (by simpa [cost] using hLower) hCostNonnegative
  intro gamma
  obtain ⟨_hCommonMass, hPlanMass, _hGammaMass, hPlanNormalize,
      _hGammaNormalize, hNormalizeTendsto⟩ :=
    fixedMassPlanNormalization
      (I := FiniteCoupling mu nu)
      (L := nhds gamma)
      (gammaNet := fun eta => eta)
      hPositive tendsto_id
  have hNormalizeIntegrable :
      forall eta : FiniteCoupling mu nu,
        Integrable cost
          (eta.plan.normalize : Measure (E × E)) := by
    intro eta
    have hPlanNonzero : eta.plan ≠ 0 := by
      apply eta.plan.mass_nonzero_iff.mp
      rw [hPlanMass eta]
      exact ne_of_gt hPositive
    rw [eta.plan.toMeasure_normalize_eq_of_nonzero hPlanNonzero]
    exact (hIntegrable eta).smul_measure_nnreal
  have hNormalizedLintegralLower :
      LowerSemicontinuousAt
        (fun eta : FiniteCoupling mu nu =>
          ∫⁻ z, ENNReal.ofReal (cost z)
            ∂(eta.plan.normalize : Measure (E × E)))
        gamma := by
    have hNormalizeContinuous :
        ContinuousAt
          (fun eta : FiniteCoupling mu nu => eta.plan.normalize)
          gamma :=
      hNormalizeTendsto
    simpa [Function.comp_def] using
      LowerSemicontinuousAt.comp
        (g := fun eta : FiniteCoupling mu nu => eta.plan.normalize)
        (x := gamma)
        (hProbabilityLower gamma.plan.normalize) hNormalizeContinuous
  have hNormalizedIntegralLower :
      LowerSemicontinuousAt normalizedIntegral gamma := by
    intro r hr
    by_cases hrNegative : r < 0
    · exact Filter.Eventually.of_forall fun eta =>
        hrNegative.trans_le (integral_nonneg hCostNonnegative)
    · have hrNonnegative : 0 <= r := le_of_not_gt hrNegative
      have hENNRealStrict :
          ENNReal.ofReal r <
            ∫⁻ z, ENNReal.ofReal (cost z)
              ∂(gamma.plan.normalize : Measure (E × E)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal
          (hNormalizeIntegrable gamma)
          (ae_of_all _ hCostNonnegative)]
        exact
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hrNonnegative).2 hr
      filter_upwards
        [hNormalizedLintegralLower
          (ENNReal.ofReal r) hENNRealStrict] with eta hEta
      rw [← ofReal_integral_eq_lintegral_ofReal
        (hNormalizeIntegrable eta)
        (ae_of_all _ hCostNonnegative)] at hEta
      exact
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hrNonnegative).1 hEta
  have hNormalizeIntegral :
      forall eta : FiniteCoupling mu nu,
        profileCost profile eta =
          (mu.mass : Real) * normalizedIntegral eta := by
    intro eta
    change
      (∫ z, cost z ∂(eta.plan : Measure (E × E))) =
        (mu.mass : Real) * normalizedIntegral eta
    rw [hPlanNormalize eta]
    simp [normalizedIntegral,
      FiniteMeasure.toMeasure_smul, NNReal.smul_def]
  intro r hr
  have hMassReal : 0 < (mu.mass : Real) := by
    exact_mod_cast hPositive
  have hThreshold :
      r / (mu.mass : Real) < normalizedIntegral gamma := by
    apply (div_lt_iff₀ hMassReal).2
    rw [mul_comm, ← hNormalizeIntegral gamma]
    exact hr
  filter_upwards
    [hNormalizedIntegralLower
      (r / (mu.mass : Real)) hThreshold] with eta hEta
  have hScaled := (div_lt_iff₀ hMassReal).1 hEta
  rwa [mul_comm, ← hNormalizeIntegral eta] at hScaled

/-- Every member of an admissible perturbation family is itself an
admissible strictly-concave profile. Its lower-growth witness is zero because
the family is nonnegative. -/
theorem perturbationProfile_admissibleStrictlyConcave
    {family : Real -> Real -> Real} {firstOrder : Real -> Real}
    (hFamily : PerturbationAssumptions family firstOrder)
    {epsilon : Real} (hEpsilon : epsilon ∈ epsilonDomain) :
    AdmissibleStrictlyConcaveProfile (family epsilon) := by
  refine ⟨hFamily.strictlyConcave hEpsilon, 0, le_rfl, ?_⟩
  intro d hd
  have hNonnegative := hFamily.nonnegative hEpsilon hd
  linarith

/-- Every member of an admissible perturbation family attains a global
minimum on the fixed-marginal coupling space. -/
theorem exists_perturbationProfileMinimizer
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    {family : Real -> Real -> Real} {firstOrder : Real -> Real}
    (hFamily : PerturbationAssumptions family firstOrder)
    {epsilon : Real} (hEpsilon : epsilon ∈ epsilonDomain) :
    exists gamma : FiniteCoupling mu nu,
      IsProfileMinimizer (family epsilon) gamma := by
  obtain ⟨gamma₀⟩ :=
    nonempty_finiteCoupling_of_equal_positive_mass
      mu nu hMarginals.equalMass hMarginals.positiveMass
  have hStrictProfile :=
    perturbationProfile_admissibleStrictlyConcave hFamily hEpsilon
  have hProfile : AdmissibleConcaveProfile (family epsilon) :=
    ⟨hStrictProfile.1.concaveOn, hStrictProfile.2⟩
  have hCost :
      LowerSemicontinuous
        (profileCost (family epsilon) :
          FiniteCoupling mu nu -> Real) :=
    profileCost_lowerSemicontinuous_of_nonnegative
      hMarginals.positiveMass
      (concaveProfileDistanceLowerSemicontinuous hProfile.1)
      (fun hd => hFamily.nonnegative hEpsilon hd)
      (fun gamma =>
        admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
          hProfile hMarginals.sourceFirstMoment
            hMarginals.targetFirstMoment gamma)
  have hUnivNonempty :
      (Set.univ : Set (FiniteCoupling mu nu)).Nonempty :=
    ⟨gamma₀, Set.mem_univ gamma₀⟩
  obtain ⟨gamma, hGammaMem, hGammaMin⟩ :=
    (hCost.lowerSemicontinuousOn Set.univ).exists_isMinOn
      hUnivNonempty (finiteCouplingIsCompact mu nu)
  exact ⟨gamma, hGammaMem, hGammaMin⟩

/-- For an admissible perturbation family, graphness of every minimizer is
the only missing input for an `OptimizerFamily`. Existence, integrability,
and uniqueness are derived internally. -/
theorem nonempty_optimizerFamily_of_perturbation_graph_minimizers
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    {family : Real -> Real -> Real} {firstOrder : Real -> Real}
    (hFamily : PerturbationAssumptions family firstOrder)
    (hGraph :
      forall epsilon, epsilon ∈ epsilonDomain ->
        forall gamma : FiniteCoupling mu nu,
          IsProfileMinimizer (family epsilon) gamma ->
            exists T : Euclidean n -> Euclidean n,
              IsGraphPlan gamma T) :
    Nonempty (OptimizerFamily mu nu family) := by
  apply nonempty_optimizerFamily_of_minimizers_and_graph
    mu nu family
  · intro epsilon hEpsilon
    exact exists_perturbationProfileMinimizer
      n mu nu hMarginals hFamily hEpsilon
  · intro epsilon hEpsilon gamma
    have hStrictProfile :=
      perturbationProfile_admissibleStrictlyConcave
        hFamily hEpsilon
    have hProfile : AdmissibleConcaveProfile (family epsilon) :=
      ⟨hStrictProfile.1.concaveOn, hStrictProfile.2⟩
    exact
      admissibleConcaveProfileCostIntegrableOfMarginalFirstMoments
        hProfile hMarginals.sourceFirstMoment
          hMarginals.targetFirstMoment gamma
  · exact hGraph

/-- Direct perturbation-family adapter with an explicit uniqueness premise. -/
theorem nonempty_optimizerFamily_of_perturbation_graph_unique_minimizers
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    {family : Real -> Real -> Real} {firstOrder : Real -> Real}
    (hFamily : PerturbationAssumptions family firstOrder)
    (hGraphUnique :
      forall epsilon, epsilon ∈ epsilonDomain ->
        forall gamma : FiniteCoupling mu nu,
          IsProfileMinimizer (family epsilon) gamma ->
            (exists T : Euclidean n -> Euclidean n,
              IsGraphPlan gamma T) /\
            forall eta : FiniteCoupling mu nu,
              IsProfileMinimizer (family epsilon) eta ->
                eta = gamma) :
    Nonempty (OptimizerFamily mu nu family) := by
  apply nonempty_optimizerFamily_of_minimizers_and_graph_unique
    mu nu family
  · intro epsilon hEpsilon
    exact exists_perturbationProfileMinimizer
      n mu nu hMarginals hFamily hEpsilon
  · exact hGraphUnique

/-- A graphness/uniqueness theorem for each admissible perturbation profile
supplies exactly the optimizer-family producer expected by
`mainConvergence_of_producers`. -/
theorem optimizerFamilyProducer_of_perturbation_graph_unique_minimizers
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (hGraphUnique :
      forall (family : Real -> Real -> Real)
        (firstOrder : Real -> Real),
        PerturbationAssumptions family firstOrder ->
          forall epsilon, epsilon ∈ epsilonDomain ->
            forall gamma : FiniteCoupling mu nu,
              IsProfileMinimizer (family epsilon) gamma ->
                (exists T : Euclidean n -> Euclidean n,
                  IsGraphPlan gamma T) /\
                forall eta : FiniteCoupling mu nu,
                  IsProfileMinimizer (family epsilon) eta ->
                    eta = gamma) :
    forall family : Real -> Real -> Real,
      (exists firstOrder : Real -> Real,
        PerturbationAssumptions family firstOrder) ->
          Nonempty (OptimizerFamily mu nu family) := by
  intro family hFamily
  obtain ⟨firstOrder, hAssumptions⟩ := hFamily
  exact
    nonempty_optimizerFamily_of_perturbation_graph_unique_minimizers
      n mu nu hMarginals hAssumptions
        (hGraphUnique family firstOrder hAssumptions)

/-- A graphness theorem for every minimizer of every admissible perturbation
profile supplies the optimizer-family producer expected by
`mainConvergence_of_producers`. -/
theorem optimizerFamilyProducer_of_perturbation_graph_minimizers
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (hGraph :
      forall (family : Real -> Real -> Real)
        (firstOrder : Real -> Real),
        PerturbationAssumptions family firstOrder ->
          forall epsilon, epsilon ∈ epsilonDomain ->
            forall gamma : FiniteCoupling mu nu,
              IsProfileMinimizer (family epsilon) gamma ->
                exists T : Euclidean n -> Euclidean n,
                  IsGraphPlan gamma T) :
    forall family : Real -> Real -> Real,
      (exists firstOrder : Real -> Real,
        PerturbationAssumptions family firstOrder) ->
          Nonempty (OptimizerFamily mu nu family) := by
  intro family hFamily
  obtain ⟨firstOrder, hAssumptions⟩ := hFamily
  exact
    nonempty_optimizerFamily_of_perturbation_graph_minimizers
      n mu nu hMarginals hAssumptions
        (hGraph family firstOrder hAssumptions)

/-- A positive power below one has at most affine growth on the
nonnegative half-line. -/
theorem powerProfile_le_one_add
    {epsilon r : Real} (hEpsilon : epsilon ∈ epsilonDomain) (hr : 0 <= r) :
    powerProfile epsilon r <= 1 + r := by
  have hExponentNonnegative : 0 <= 1 - epsilon := by
    linarith [hEpsilon.2]
  by_cases hrOne : r <= 1
  · have hPowerLeOne :
        powerProfile epsilon r <= 1 := by
      exact Real.rpow_le_one hr hrOne hExponentNonnegative
    linarith
  · have hOne : 1 <= r := le_of_not_ge hrOne
    have hPowerLeSelf :
        powerProfile epsilon r <= r := by
      unfold powerProfile
      exact Real.rpow_le_self_of_one_le hOne (by linarith [hEpsilon.1])
    linarith

/-- Marginal logarithmic moments make every power profile in
`epsilonDomain` integrable under every finite coupling. -/
theorem powerProfileCostIntegrableOfMarginalLogMoments
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    [SecondCountableTopology E]
    {mu nu : FiniteMeasure E}
    (hMu : Integrable (fun x : E => Psi ‖x‖) (mu : Measure E))
    (hNu : Integrable (fun y : E => Psi ‖y‖) (nu : Measure E))
    (gamma : FiniteCoupling mu nu)
    {epsilon : Real} (hEpsilon : epsilon ∈ epsilonDomain) :
    Integrable
      (fun z : E × E => powerProfile epsilon ‖z.1 - z.2‖)
      (gamma.plan : Measure (E × E)) := by
  have hDistance :=
    distanceCostIntegrableOfMarginalLogMoments hMu hNu gamma
  have hDominating :
      Integrable (fun z : E × E => 1 + ‖z.1 - z.2‖)
        (gamma.plan : Measure (E × E)) :=
    (integrable_const 1).add hDistance
  refine hDominating.mono' ?_ (ae_of_all _ fun z => ?_)
  · have hContinuous :=
      (powerProfile_strictConcaveRadialProfileAssumptions hEpsilon).continuous
    exact
      (hContinuous.measurable.comp
        ((measurable_fst.sub measurable_snd).norm)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg
      ((powerProfile_strictConcaveRadialProfileAssumptions hEpsilon).nonnegative
        (norm_nonneg (z.1 - z.2)))]
    exact powerProfile_le_one_add
      (epsilon := epsilon) (r := ‖z.1 - z.2‖)
      hEpsilon (norm_nonneg (z.1 - z.2))

/-- Every power profile in `epsilonDomain` attains its minimum on the
fixed-marginal coupling space. This is the standard compactness part of the
optimizer theorem and does not use graphness or uniqueness. -/
theorem exists_powerProfileMinimizer
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu)
    {epsilon : Real} (hEpsilon : epsilon ∈ epsilonDomain) :
    exists gamma : FiniteCoupling mu nu,
      IsProfileMinimizer (powerProfile epsilon) gamma := by
  obtain ⟨gamma₀⟩ :=
    nonempty_finiteCoupling_of_equal_positive_mass
      mu nu hPower.equalMass hPower.positiveMass
  have hProfile :=
    powerProfile_strictConcaveRadialProfileAssumptions hEpsilon
  have hCostLower :
      LowerSemicontinuous
        (fun z : Euclidean n × Euclidean n =>
          powerProfile epsilon ‖z.1 - z.2‖) :=
    (hProfile.continuous.comp
      ((continuous_fst.sub continuous_snd).norm)).lowerSemicontinuous
  have hCost :
      LowerSemicontinuous
        (profileCost (powerProfile epsilon) :
          FiniteCoupling mu nu -> Real) :=
    profileCost_lowerSemicontinuous_of_nonnegative
      hPower.positiveMass hCostLower hProfile.nonnegative
      (fun gamma =>
        powerProfileCostIntegrableOfMarginalLogMoments
          hPower.sourceLogMoment hPower.targetLogMoment gamma hEpsilon)
  have hUnivNonempty :
      (Set.univ : Set (FiniteCoupling mu nu)).Nonempty :=
    ⟨gamma₀, Set.mem_univ gamma₀⟩
  obtain ⟨gamma, hGammaMem, hGammaMin⟩ :=
    (hCost.lowerSemicontinuousOn Set.univ).exists_isMinOn
      hUnivNonempty (finiteCouplingIsCompact mu nu)
  exact ⟨gamma, hGammaMem, hGammaMin⟩

/-- The exact remaining power-optimizer premise after compactness,
integrability, and the midpoint argument: every minimizer is induced by a
measurable map. -/
theorem nonempty_powerOptimizerFamily_of_graph_minimizers
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu)
    (hGraph :
      forall epsilon, epsilon ∈ epsilonDomain ->
        forall gamma : FiniteCoupling mu nu,
          IsProfileMinimizer (powerProfile epsilon) gamma ->
            exists T : Euclidean n -> Euclidean n,
              IsGraphPlan gamma T) :
    Nonempty (OptimizerFamily mu nu powerProfile) := by
  apply nonempty_optimizerFamily_of_minimizers_and_graph
    mu nu powerProfile
  · intro epsilon hEpsilon
    exact exists_powerProfileMinimizer
      n mu nu hPower hEpsilon
  · intro epsilon hEpsilon gamma
    exact
      powerProfileCostIntegrableOfMarginalLogMoments
        hPower.sourceLogMoment hPower.targetLogMoment
          gamma hEpsilon
  · exact hGraph

/-- Direct power-family adapter with an explicit uniqueness premise. -/
theorem nonempty_powerOptimizerFamily_of_graph_unique_minimizers
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu)
    (hGraphUnique :
      forall epsilon, epsilon ∈ epsilonDomain ->
        forall gamma : FiniteCoupling mu nu,
          IsProfileMinimizer (powerProfile epsilon) gamma ->
            (exists T : Euclidean n -> Euclidean n,
              IsGraphPlan gamma T) /\
            forall eta : FiniteCoupling mu nu,
              IsProfileMinimizer (powerProfile epsilon) eta ->
                eta = gamma) :
    Nonempty (OptimizerFamily mu nu powerProfile) := by
  apply nonempty_optimizerFamily_of_minimizers_and_graph_unique
    mu nu powerProfile
  · intro epsilon hEpsilon
    exact exists_powerProfileMinimizer n mu nu hPower hEpsilon
  · exact hGraphUnique

/-- A profile-uniform Gangbo--McCann/Pegon theorem implies the exact
power-specific premise above. The elementary profile hypotheses are supplied
by `powerProfile_strictConcaveRadialProfileAssumptions`. -/
theorem nonempty_powerOptimizerFamily_of_strictConcaveRadial_graph_unique
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu)
    (hRadialGraphUnique :
      forall profile : Real -> Real,
        StrictConcaveRadialProfileAssumptions profile ->
          forall gamma : FiniteCoupling mu nu,
            IsProfileMinimizer profile gamma ->
              (exists T : Euclidean n -> Euclidean n,
                IsGraphPlan gamma T) /\
              forall eta : FiniteCoupling mu nu,
                IsProfileMinimizer profile eta ->
                  eta = gamma) :
    Nonempty (OptimizerFamily mu nu powerProfile) := by
  apply nonempty_powerOptimizerFamily_of_graph_unique_minimizers
    n mu nu hPower
  intro epsilon hEpsilon gamma hGamma
  exact
    hRadialGraphUnique (powerProfile epsilon)
      (powerProfile_strictConcaveRadialProfileAssumptions hEpsilon)
      gamma hGamma

/-- A profile-uniform Gangbo--McCann/Pegon graph theorem implies the
power-specific graphness premise. All elementary profile hypotheses are
verified for `powerProfile` on `epsilonDomain`. -/
theorem nonempty_powerOptimizerFamily_of_strictConcaveRadial_graph
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu)
    (hRadialGraph :
      forall profile : Real -> Real,
        StrictConcaveRadialProfileAssumptions profile ->
          forall gamma : FiniteCoupling mu nu,
            IsProfileMinimizer profile gamma ->
              exists T : Euclidean n -> Euclidean n,
                IsGraphPlan gamma T) :
    Nonempty (OptimizerFamily mu nu powerProfile) := by
  apply nonempty_powerOptimizerFamily_of_graph_minimizers
    n mu nu hPower
  intro epsilon hEpsilon gamma hGamma
  exact
    hRadialGraph (powerProfile epsilon)
      (powerProfile_strictConcaveRadialProfileAssumptions hEpsilon)
      gamma hGamma

end ConcaveOTLimit

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Instances.EReal.Lemmas

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace ConcaveOTLimit

/-! ## Measures, couplings, and transport objectives -/

abbrev Euclidean (n : Nat) := EuclideanSpace Real (Fin n)

instance instMeasurableSpaceEuclidean (n : Nat) :
    MeasurableSpace (Euclidean n) :=
  borel (Euclidean n)

instance instBorelSpaceEuclidean (n : Nat) :
    BorelSpace (Euclidean n) :=
  ⟨rfl⟩

def firstMarginal {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (gamma : FiniteMeasure (X × Y)) : FiniteMeasure X :=
  gamma.map Prod.fst

def secondMarginal {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (gamma : FiniteMeasure (X × Y)) : FiniteMeasure Y :=
  gamma.map Prod.snd

def IsFiniteCoupling {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : FiniteMeasure X) (nu : FiniteMeasure Y)
    (gamma : FiniteMeasure (X × Y)) : Prop :=
  firstMarginal gamma = mu /\ secondMarginal gamma = nu

def FiniteCoupling {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : FiniteMeasure X) (nu : FiniteMeasure Y) :=
  {gamma : FiniteMeasure (X × Y) // IsFiniteCoupling mu nu gamma}

namespace FiniteCoupling

def plan {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu) : FiniteMeasure (X × Y) :=
  gamma.1

end FiniteCoupling

instance instTopologicalSpaceFiniteCoupling
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace X] [TopologicalSpace Y]
    [OpensMeasurableSpace (X × Y)]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y} :
    TopologicalSpace (FiniteCoupling mu nu) :=
  inferInstanceAs
    (TopologicalSpace
      {gamma : FiniteMeasure (X × Y) //
        IsFiniteCoupling mu nu gamma})

def finiteGraphPlan {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : FiniteMeasure X) (T : X -> Y) (_hT : Measurable T) :
    FiniteMeasure (X × Y) :=
  mu.map fun x => (x, T x)

def IsGraphPlan {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu) (T : X -> Y) : Prop :=
  exists hT : Measurable T,
    gamma.plan = finiteGraphPlan mu T hT

def IsSupported {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu) (S : Set (X × Y)) : Prop :=
  ∀ᵐ z ∂(gamma.plan : Measure (X × Y)), z ∈ S

def profileCost {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    {mu nu : FiniteMeasure E} (profile : Real -> Real)
    (gamma : FiniteCoupling mu nu) : Real :=
  integral (gamma.plan : Measure (E × E))
    fun z => profile ‖z.1 - z.2‖

def distanceCost {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    {mu nu : FiniteMeasure E} (gamma : FiniteCoupling mu nu) : Real :=
  profileCost id gamma

def IsMinimizerOn {X : Type*} (A : Set X) (F : X -> Real) (x : X) : Prop :=
  x ∈ A /\ ∀ y ∈ A, F x <= F y

def IsUniqueMinimizerOn {X : Type*}
    (A : Set X) (F : X -> Real) (x : X) : Prop :=
  IsMinimizerOn A F x /\
    ∀ y, IsMinimizerOn A F y -> y = x

def IsProfileMinimizer {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] {mu nu : FiniteMeasure E}
    (profile : Real -> Real) (gamma : FiniteCoupling mu nu) : Prop :=
  IsMinimizerOn univ (profileCost profile) gamma

def IsUniqueProfileMinimizer {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] {mu nu : FiniteMeasure E}
    (profile : Real -> Real) (gamma : FiniteCoupling mu nu) : Prop :=
  IsUniqueMinimizerOn univ (profileCost profile) gamma

def IsDistanceOptimal {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] {mu nu : FiniteMeasure E}
    (gamma : FiniteCoupling mu nu) : Prop :=
  IsProfileMinimizer id gamma

def distanceOptimalFace {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] (mu nu : FiniteMeasure E) :
    Set (FiniteCoupling mu nu) :=
  {gamma | IsDistanceOptimal gamma}

def IsSecondaryMinimizer {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] {mu nu : FiniteMeasure E}
    (profile : Real -> Real) (gamma : FiniteCoupling mu nu) : Prop :=
  IsMinimizerOn (distanceOptimalFace mu nu) (profileCost profile) gamma

def IsUniqueSecondaryMinimizer {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] {mu nu : FiniteMeasure E}
    (profile : Real -> Real) (gamma : FiniteCoupling mu nu) : Prop :=
  IsUniqueMinimizerOn
    (distanceOptimalFace mu nu) (profileCost profile) gamma

/-! ## Assumptions on marginals and profiles -/

def FiniteMutuallySingular {X : Type*} [MeasurableSpace X]
    (mu nu : FiniteMeasure X) : Prop :=
  exists A : Set X, MeasurableSet A /\
    (mu : Measure X) Aᶜ = 0 /\ (nu : Measure X) A = 0

structure MarginalHypotheses (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n)) : Prop where
  equalMass : mu.mass = nu.mass
  positiveMass : 0 < mu.mass
  mutuallySingular : FiniteMutuallySingular mu nu
  sourceAbsolutelyContinuous :
    (mu : Measure (Euclidean n)) ≪ volume
  sourceFirstMoment :
    Integrable (fun x : Euclidean n => ‖x‖)
      (mu : Measure (Euclidean n))
  targetFirstMoment :
    Integrable (fun y : Euclidean n => ‖y‖)
      (nu : Measure (Euclidean n))

def epsilonDomain : Set Real := Ioo 0 1

structure PerturbationAssumptions
    (family : Real -> Real -> Real) (firstOrder : Real -> Real) : Prop where
  nonnegative :
    ∀ {eps d : Real}, eps ∈ epsilonDomain -> 0 <= d ->
      0 <= family eps d
  increasing :
    ∀ {eps : Real}, eps ∈ epsilonDomain ->
      MonotoneOn (family eps) (Ici 0)
  strictlyConcave :
    ∀ {eps : Real}, eps ∈ epsilonDomain ->
      StrictConcaveOn Real (Ici 0) (family eps)
  convexInEpsilon :
    ∀ {d : Real}, 0 <= d ->
      ConvexOn Real epsilonDomain fun eps => family eps d
  tendsToIdentity :
    ∀ {d : Real}, 0 <= d ->
      Tendsto (fun eps => family eps d)
        (nhdsWithin 0 epsilonDomain) (nhds d)
  firstOrderLimit :
    ∀ {d : Real}, 0 <= d ->
      Tendsto (fun eps => (family eps d - d) / eps)
        (nhdsWithin 0 epsilonDomain) (nhds (firstOrder d))
  firstOrderStrictlyConcave :
    StrictConcaveOn Real (Ici 0) firstOrder
  firstOrderLowerBound :
    exists C : Real, 0 <= C /\
      ∀ {d : Real}, 0 <= d ->
        -C * (1 + d) <= firstOrder d
  growth :
    ∀ {eps d : Real}, eps ∈ epsilonDomain -> 0 <= d ->
      family eps d <= 2 * (1 + d)

def AdmissibleConcaveProfile (profile : Real -> Real) : Prop :=
  ConcaveOn Real (Ici 0) profile /\
    exists C : Real, 0 <= C /\
      ∀ {d : Real}, 0 <= d -> -C * (1 + d) <= profile d

def AdmissibleStrictlyConcaveProfile (profile : Real -> Real) : Prop :=
  StrictConcaveOn Real (Ici 0) profile /\
    exists C : Real, 0 <= C /\
      ∀ {d : Real}, 0 <= d -> -C * (1 + d) <= profile d

def IsIntrinsicGeneralizedECPlan {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] (mu nu : FiniteMeasure E)
    (gammaSharp : FiniteCoupling mu nu) : Prop :=
  ∀ profile : Real -> Real,
    AdmissibleStrictlyConcaveProfile profile ->
      IsUniqueSecondaryMinimizer profile gammaSharp

structure OptimizerFamily {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] (mu nu : FiniteMeasure E)
    (family : Real -> Real -> Real) where
  plan : Real -> FiniteCoupling mu nu
  transportMap : Real -> E -> E
  graph :
    ∀ eps ∈ epsilonDomain,
      IsGraphPlan (plan eps) (transportMap eps)
  uniquelyOptimal :
    ∀ eps ∈ epsilonDomain,
      IsUniqueProfileMinimizer (family eps) (plan eps)

/-! ## Sequential Gamma convergence -/

structure SequentialGammaConvergesOn
    {X : Type*} [TopologicalSpace X]
    (approximation : Nat -> X -> EReal)
    (limit : X -> EReal) (domain : Set X) : Prop where
  liminf :
    ∀ {xSeq : Nat -> X} {x : X} {subseq : Nat -> Nat},
      StrictMono subseq ->
        Tendsto xSeq atTop (nhds x) ->
          x ∈ domain ->
            ∀ r : Real, (r : EReal) < limit x ->
              ∀ᶠ k in atTop,
                (r : EReal) <= approximation (subseq k) (xSeq k)
  recovery :
    ∀ x ∈ domain, exists xSeq : Nat -> X,
      Tendsto xSeq atTop (nhds x) /\
        Tendsto (fun k => approximation k (xSeq k))
          atTop (nhds (limit x))

abbrev SequentialGammaConverges
    {X : Type*} [TopologicalSpace X]
    (approximation : Nat -> X -> EReal)
    (limit : X -> EReal) : Prop :=
  SequentialGammaConvergesOn approximation limit univ

def IsEquicoercive
    {I X : Type*} [TopologicalSpace X]
    (functional : I -> X -> EReal) : Prop :=
  ∀ r : Real, exists K : Set X,
    IsCompact K /\
      ∀ i x, functional i x <= (r : EReal) -> x ∈ K

def minimalDistanceCost {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] (mu nu : FiniteMeasure E) : Real :=
  sInf (Set.range fun gamma : FiniteCoupling mu nu =>
    distanceCost gamma)

def rescaledProfileCost {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] {mu nu : FiniteMeasure E}
    (family : Real -> Real -> Real) (eps : Real)
    (gamma : FiniteCoupling mu nu) : Real :=
  (profileCost (family eps) gamma -
    minimalDistanceCost mu nu) / eps

def extendedSecondaryCost {E : Type*} [MeasurableSpace E]
    [NormedAddCommGroup E] {mu nu : FiniteMeasure E}
    (profile : Real -> Real) (gamma : FiniteCoupling mu nu) : EReal :=
  by
    classical
    exact if IsDistanceOptimal gamma then
      (profileCost profile gamma : EReal)
    else
      ⊤

/-! ## The power-cost branch -/

def Psi (r : Real) : Real := r * Real.log (1 + r)

def logarithmicProfile (r : Real) : Real := Real.negMulLog r

def powerProfile (eps r : Real) : Real := r ^ (1 - eps)

structure PowerMarginalHypotheses (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n)) : Prop where
  equalMass : mu.mass = nu.mass
  positiveMass : 0 < mu.mass
  mutuallySingular : FiniteMutuallySingular mu nu
  sourceAbsolutelyContinuous :
    (mu : Measure (Euclidean n)) ≪ volume
  sourceLogMoment :
    Integrable (fun x : Euclidean n => Psi ‖x‖)
      (mu : Measure (Euclidean n))
  targetLogMoment :
    Integrable (fun y : Euclidean n => Psi ‖y‖)
      (nu : Measure (Euclidean n))

/-! ## One-dimensional excursion couplings -/

def IsAtomlessFinite {X : Type*} [MeasurableSpace X]
    (mu : FiniteMeasure X) : Prop :=
  ∀ x, (mu : Measure X) {x} = 0

def cumulative (mu : FiniteMeasure Real) (x : Real) : ENNReal :=
  (mu : Measure Real) (Iic x)

def StochasticallyDominates
    (nu mu : FiniteMeasure Real) : Prop :=
  ∀ x, cumulative nu x <= cumulative mu x

def IsForwardPlan {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu) : Prop :=
  ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.1 <= z.2

def ArchesDoNotCross (p q : Real × Real) : Prop :=
  Disjoint (uIcc p.1 p.2) (uIcc q.1 q.2) \/
    (exists z, uIcc p.1 p.2 ∩ uIcc q.1 q.2 = {z}) \/
    uIcc p.1 p.2 ⊆ uIcc q.1 q.2 \/
    uIcc q.1 q.2 ⊆ uIcc p.1 p.2

def ArchesDoNotConnect (p q : Real × Real) : Prop :=
  min |p.2 - p.1| |q.2 - q.1| > 0 -> p.2 ≠ q.1

def NestedArchesHaveSameOrientation (p q : Real × Real) : Prop :=
  uIcc q.1 q.2 ⊆ uIoo p.1 p.2 ->
    0 <= (p.2 - p.1) * (q.2 - q.1)

def IsMonotoneArchSet (S : Set (Real × Real)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S,
    ArchesDoNotCross p q /\
      ArchesDoNotConnect p q /\
      NestedArchesHaveSameOrientation p q

def IsJuilletExcursionPlan
    (mu nu : FiniteMeasure Real)
    (gamma : FiniteMeasure (Real × Real)) : Prop :=
  IsFiniteCoupling mu nu gamma /\
    exists S : Set (Real × Real), MeasurableSet S /\
      (∀ᵐ z ∂(gamma : Measure (Real × Real)), z ∈ S) /\
      IsMonotoneArchSet S

/-! ## Oriented maximal transport rays -/

def rayDirection {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] (x y : E) : E :=
  NormedSpace.normalize (y - x)

def transportSet {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] (Gamma : Set (E × E)) : Set E :=
  {z | exists p : E × E,
    p ∈ Gamma /\ p.1 ≠ p.2 /\ z ∈ openSegment Real p.1 p.2}

def leftTransportSet {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] (Gamma : Set (E × E)) : Set E :=
  {z | exists p : E × E,
    p ∈ Gamma /\ p.1 ≠ p.2 /\
      z ∈ segment Real p.1 p.2 /\ z ≠ p.2}

def NoCrossing {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] (Gamma : Set (E × E)) : Prop :=
  ∀ x y x' y',
    (x, y) ∈ Gamma ->
    (x', y') ∈ Gamma ->
    x ≠ y ->
    x' ≠ y' ->
    rayDirection x y ≠ rayDirection x' y' ->
    (segment Real x y ∩ segment Real x' y').Nonempty ->
    x = x' \/ y = y'

abbrev RawRayCode (n : Nat) :=
  (Euclidean n × Euclidean n) × (EReal × EReal)

def IsRayCode {n : Nat} (p : RawRayCode n) : Prop :=
  ‖p.1.2‖ = 1 /\
    inner Real p.1.1 p.1.2 = 0 /\
    p.2.1 < p.2.2

abbrev OrientedOpenRay (n : Nat) :=
  {p : RawRayCode n // IsRayCode p}

namespace OrientedOpenRay

def anchor {n : Nat} (R : OrientedOpenRay n) : Euclidean n :=
  R.1.1.1

def direction {n : Nat} (R : OrientedOpenRay n) : Euclidean n :=
  R.1.1.2

def point {n : Nat} (R : OrientedOpenRay n) (t : Real) : Euclidean n :=
  R.anchor + t • R.direction

def lower {n : Nat} (R : OrientedOpenRay n) : EReal :=
  R.1.2.1

def upper {n : Nat} (R : OrientedOpenRay n) : EReal :=
  R.1.2.2

def carrier {n : Nat} (R : OrientedOpenRay n) : Set (Euclidean n) :=
  {z | exists t : Real,
    R.lower < (t : EReal) /\ (t : EReal) < R.upper /\
      R.point t = z}

def CoveredBy {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (R : OrientedOpenRay n) : Prop :=
  ∀ z, z ∈ R.carrier ->
    exists x y : Euclidean n,
      (x, y) ∈ Gamma /\ x ≠ y /\
        z ∈ openSegment Real x y /\
        rayDirection x y = R.direction

def IsMaximalTransportRay {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (R : OrientedOpenRay n) : Prop :=
  R.CoveredBy Gamma /\
    ∀ S : OrientedOpenRay n,
      R.carrier ⊆ S.carrier ->
      S.CoveredBy Gamma ->
      S.carrier ⊆ R.carrier

end OrientedOpenRay

def IsMaximalRayAssignment {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (pi : transportSet Gamma -> OrientedOpenRay n) : Prop :=
  ∀ z,
    (pi z).IsMaximalTransportRay Gamma /\
      z.1 ∈ (pi z).carrier

def OrientedBefore {n : Nat} (R : OrientedOpenRay n)
    (x y : Euclidean n) : Prop :=
  exists s t : Real, s <= t /\ x = R.point s /\ y = R.point t

def distanceContactSet {E : Type*} [PseudoMetricSpace E]
    (u : E -> Real) : Set (E × E) :=
  {z | dist z.1 z.2 = u z.1 - u z.2}

def IsDistanceCyclicallyMonotone {E : Type*} [PseudoMetricSpace E]
    (S : Set (E × E)) : Prop :=
  ∀ {I : Type*} [Fintype I] (x y : I -> E),
    (∀ i, (x i, y i) ∈ S) ->
      ∀ sigma : Equiv.Perm I,
        (∑ i, dist (x i) (y i)) <=
          ∑ i, dist (x i) (y (sigma i))

structure RayRegularityHypotheses {n : Nat}
    (rho : Measure (Euclidean n))
    (Gamma : Set (Euclidean n × Euclidean n)) where
  noCrossing : NoCrossing Gamma
  directionField : Euclidean n -> Euclidean n
  directionAgrees :
    ∀ z ∈ transportSet Gamma,
      ∀ x y, (x, y) ∈ Gamma ->
        z ∈ openSegment Real x y ->
          directionField z = rayDirection x y
  leftEndpointNegligible :
    rho (leftTransportSet Gamma \ transportSet Gamma) = 0
  exceptional : Set (Euclidean n)
  exceptionalNegligible : rho exceptional = 0
  exceptionalSubset : exceptional ⊆ transportSet Gamma
  compactPiece : Nat -> Set (Euclidean n)
  compactPieceMonotone : Monotone compactPiece
  compactPieceIsCompact : ∀ k, IsCompact (compactPiece k)
  compactPieceCover :
    (iUnion compactPiece) = transportSet Gamma \ exceptional
  directionLipschitz :
    ∀ k, exists L : NNReal,
      LipschitzOnWith L directionField (compactPiece k)

def SameMaximalRayClosure {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (x y : Euclidean n) : Prop :=
  exists R : OrientedOpenRay n,
    R.IsMaximalTransportRay Gamma /\
      x ∈ closure R.carrier /\ y ∈ closure R.carrier

def rayCoordinate {n : Nat} (R : OrientedOpenRay n)
    (x : Euclidean n) : Real :=
  inner Real (x - R.anchor) R.direction

structure RaywiseExcursionDisintegration {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (mu nu : FiniteMeasure (Euclidean n))
    (gamma : FiniteMeasure (Euclidean n × Euclidean n))
    (transportMap : Euclidean n -> Euclidean n) where
  sigma : FiniteMeasure (OrientedOpenRay n)
  source : OrientedOpenRay n -> FiniteMeasure (Euclidean n)
  target : OrientedOpenRay n -> FiniteMeasure (Euclidean n)
  component :
    OrientedOpenRay n -> FiniteMeasure (Euclidean n × Euclidean n)
  sourceEvaluationMeasurable :
    ∀ s : Set (Euclidean n), MeasurableSet s ->
      Measurable fun R => (source R : Measure (Euclidean n)) s
  targetEvaluationMeasurable :
    ∀ s : Set (Euclidean n), MeasurableSet s ->
      Measurable fun R => (target R : Measure (Euclidean n)) s
  componentEvaluationMeasurable :
    ∀ s : Set (Euclidean n × Euclidean n), MeasurableSet s ->
      Measurable fun R =>
        (component R : Measure (Euclidean n × Euclidean n)) s
  sourceReconstruction :
    ∀ s : Set (Euclidean n), MeasurableSet s ->
      (mu : Measure (Euclidean n)) s =
        lintegral (sigma : Measure (OrientedOpenRay n))
          fun R => (source R : Measure (Euclidean n)) s
  targetReconstruction :
    ∀ s : Set (Euclidean n), MeasurableSet s ->
      (nu : Measure (Euclidean n)) s =
        lintegral (sigma : Measure (OrientedOpenRay n))
          fun R => (target R : Measure (Euclidean n)) s
  planReconstruction :
    ∀ s : Set (Euclidean n × Euclidean n), MeasurableSet s ->
      (gamma : Measure (Euclidean n × Euclidean n)) s =
        lintegral (sigma : Measure (OrientedOpenRay n))
          fun R =>
            (component R : Measure (Euclidean n × Euclidean n)) s
  rayIsMaximal :
    ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
      R.IsMaximalTransportRay Gamma
  componentIsCoupling :
    ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
      IsFiniteCoupling (source R) (target R) (component R)
  componentOnRay :
    ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
      ∀ᵐ z ∂(component R :
        Measure (Euclidean n × Euclidean n)),
        z.1 ∈ closure R.carrier /\ z.2 ∈ closure R.carrier
  componentAgreesWithMap :
    ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
      ∀ᵐ z ∂(component R :
        Measure (Euclidean n × Euclidean n)),
        z.2 = transportMap z.1
  coordinateSourceAtomless :
    ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
      IsAtomlessFinite ((source R).map (rayCoordinate R))
  coordinateMarginalsMutuallySingular :
    ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
      FiniteMutuallySingular
        ((source R).map (rayCoordinate R))
        ((target R).map (rayCoordinate R))
  coordinateTargetDominates :
    ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
      StochasticallyDominates
        ((target R).map (rayCoordinate R))
        ((source R).map (rayCoordinate R))
  coordinateComponentForward :
    ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
      ∀ᵐ z ∂(component R :
        Measure (Euclidean n × Euclidean n)),
        rayCoordinate R z.1 <= rayCoordinate R z.2
  componentIsExcursion :
    ∀ᵐ R ∂(sigma : Measure (OrientedOpenRay n)),
      IsJuilletExcursionPlan
        ((source R).map (rayCoordinate R))
        ((target R).map (rayCoordinate R))
        ((component R).map fun z =>
          (rayCoordinate R z.1, rayCoordinate R z.2))

end ConcaveOTLimit

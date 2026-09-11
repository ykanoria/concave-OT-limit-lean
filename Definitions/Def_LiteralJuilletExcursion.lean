import Definitions.Def_JuilletCanonicalRoutes

open MeasureTheory Set

namespace ConcaveOTLimit

/-- The entrance/first-subsequent-exit pairs in a horizontal section of the
completed graph of `F_mu - F_nu`. -/
def juilletCompletedGraphPairFiber
    (mu nu : FiniteMeasure Real) (h : Real) : Set (Real × Real) :=
  {p |
    0 < h /\
      IsGoodIncreasingCrossing mu nu p.1 h /\
        IsGoodDecreasingCrossing mu nu p.2 h /\
          AreConsecutiveAtLevel mu nu h p.1 p.2}

/-- A positive level is regular when its completed-graph section is finite
and every intersection is a genuine entrance or exit. -/
def IsJuilletRegularPositiveLevel
    (mu nu : FiniteMeasure Real) (h : Real) : Prop :=
  0 < h /\
    {x | (x, h) ∈ generalizedCumulativeGraph mu nu}.Finite /\
      ∀ x, (x, h) ∈ generalizedCumulativeGraph mu nu ->
        Xor (IsGoodIncreasingCrossing mu nu x h)
          (IsGoodDecreasingCrossing mu nu x h)

/-- Measurable branch data for Juillet's literal completed-graph
construction. At almost every positive level, the active indices enumerate
every entrance and every exit exactly once, and pair each entrance with the
first subsequent exit. -/
structure JuilletCompletedGraphPairingData
    (mu nu : FiniteMeasure Real) where
  source : Nat -> Real -> Real
  target : Nat -> Real -> Real
  active : Nat -> Set Real
  source_measurable : ∀ i, Measurable (source i)
  target_measurable : ∀ i, Measurable (target i)
  active_measurable : ∀ i, MeasurableSet (active i)
  active_positive : ∀ i, active i ⊆ Ioi 0
  regular_positive_levels :
    ∀ᵐ h ∂(volume : Measure Real).restrict (Ioi 0),
      IsJuilletRegularPositiveLevel mu nu h
  paired_ae :
    ∀ᵐ h ∂(volume : Measure Real),
      ∀ i, h ∈ active i ->
        (source i h, target i h) ∈
          juilletCompletedGraphPairFiber mu nu h
  entrances_exhaustive_unique_ae :
    ∀ᵐ h ∂(volume : Measure Real),
      ∀ x, 0 < h -> IsGoodIncreasingCrossing mu nu x h ->
        ∃! i : Nat, h ∈ active i ∧ source i h = x
  exits_exhaustive_unique_ae :
    ∀ᵐ h ∂(volume : Measure Real),
      ∀ y, 0 < h -> IsGoodDecreasingCrossing mu nu y h ->
        ∃! i : Nat, h ∈ active i ∧ target i h = y
  finite_active_ae :
    ∀ᵐ h ∂(volume : Measure Real),
      {i | h ∈ active i}.Finite

/-- The measure obtained by integrating one atom at every
entrance/first-subsequent-exit pair over positive completed-graph levels. -/
noncomputable def literalJuilletExcursionMeasure
    {mu nu : FiniteMeasure Real}
    (data : JuilletCompletedGraphPairingData mu nu) :
    Measure (Real × Real) :=
  Measure.sum fun i =>
    Measure.map (fun h => (data.source i h, data.target i h))
      ((volume : Measure Real).restrict (data.active i))

/-- A finite measure is the literal Juillet excursion coupling when it has
the prescribed marginals and is exactly the completed-graph occupation
measure. -/
def IsLiteralJuilletExcursionPlan
    (mu nu : FiniteMeasure Real)
    (gamma : FiniteMeasure (Real × Real)) : Prop :=
  IsFiniteCoupling mu nu gamma /\
    ∃ data : JuilletCompletedGraphPairingData mu nu,
      (gamma : Measure (Real × Real)) =
        literalJuilletExcursionMeasure data

/-- A ray disintegration whose coordinate components are literal Juillet
completed-graph excursion couplings. -/
structure LiteralRaywiseExcursionDisintegration {n : Nat}
    (Gamma : Set (Euclidean n × Euclidean n))
    (mu nu : FiniteMeasure (Euclidean n))
    (gamma : FiniteMeasure (Euclidean n × Euclidean n))
    (transportMap : Euclidean n -> Euclidean n) where
  base :
    RaywiseExcursionDisintegration Gamma mu nu gamma transportMap
  componentIsLiteral :
    ∀ᵐ R ∂(base.sigma : Measure (OrientedOpenRay n)),
      IsLiteralJuilletExcursionPlan
        ((base.source R).map (rayCoordinate R))
        ((base.target R).map (rayCoordinate R))
        ((base.component R).map fun z =>
          (rayCoordinate R z.1, rayCoordinate R z.2))

/-- The paper-faithful raywise meaning of a generalized EC plan: for an
off-diagonal distance-contact set, the plan disintegrates into literal
one-dimensional completed-graph excursion couplings. -/
def IsRaywiseGeneralizedECPlan {n : Nat}
    (mu nu : FiniteMeasure (Euclidean n))
    (gamma : FiniteCoupling mu nu)
    (transportMap : Euclidean n -> Euclidean n) : Prop :=
  ∃ u : Euclidean n -> Real,
    LipschitzWith 1 u /\
      ∃ Gamma : Set (Euclidean n × Euclidean n),
        Gamma =
          distanceContactSet u \
            {z : Euclidean n × Euclidean n | z.1 = z.2} /\
          IsSigmaCompact Gamma /\
            Nonempty
              (LiteralRaywiseExcursionDisintegration
                Gamma mu nu gamma.plan transportMap)

/-- The sole one-dimensional dependency in the faithful raywise theorem.
It identifies the existing variational/laminar component with Juillet's
literal completed-graph occupation measure under exactly the coordinate
hypotheses supplied by the ray disintegration. -/
def LiteralJuilletIdentificationPremise : Prop :=
  ∀ (mu nu : FiniteMeasure Real)
      (gamma : FiniteMeasure (Real × Real)),
    IsAtomlessFinite mu ->
      FiniteMutuallySingular mu nu ->
        StochasticallyDominates nu mu ->
          IsFiniteCoupling mu nu gamma ->
            (∀ᵐ z ∂(gamma : Measure (Real × Real)), z.1 <= z.2) ->
              IsJuilletExcursionPlan mu nu gamma ->
                IsLiteralJuilletExcursionPlan mu nu gamma

/-- The genuinely analytic one-dimensional construction boundary: under the
ordered mutually singular hypotheses, construct one literal completed-graph
coupling which also has the laminar support property. Direct coupling
uniqueness then identifies it with every variational ray component. -/
def LiteralJuilletConstructionPremise : Prop :=
  ∀ (mu nu : FiniteMeasure Real),
    mu.mass = nu.mass ->
      IsAtomlessFinite mu ->
        FiniteMutuallySingular mu nu ->
          StochasticallyDominates nu mu ->
            ∃ gamma : FiniteMeasure (Real × Real),
              IsLiteralJuilletExcursionPlan mu nu gamma /\
                IsJuilletExcursionPlan mu nu gamma

end ConcaveOTLimit

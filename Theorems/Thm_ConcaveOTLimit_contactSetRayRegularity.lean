import Theorems.Thm_ConcaveOTLimit_distanceContactCoveredRaySaturation
import Theorems.Thm_ConcaveOTLimit_distanceContactSubsetNoCrossing
import Theorems.Thm_ConcaveOTLimit_existsMeasurableSegmentwiseLipschitzDirectionField
import Theorems.Thm_ConcaveOTLimit_contactDirectionCompactExhaustion
import Theorems.Thm_ConcaveOTLimit_contactEndpointNullity

open MeasureTheory Set

namespace ConcaveOTLimit

/-- The compact-exhaustion data in `RayRegularityHypotheses`, separated from
the contact geometry and endpoint-nullity statements. -/
structure RayDirectionCompactExhaustion {n : Nat}
    (rho : Measure (Euclidean n))
    (Gamma : Set (Euclidean n × Euclidean n))
    (directionField : Euclidean n -> Euclidean n) where
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

/-- A fixed measurable canonical direction field supplied by the pinned
segmentwise direction theorem. -/
noncomputable def contactSetDirectionField {n : Nat}
    (u : Euclidean n -> Real)
    (hu : LipschitzWith 1 u)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hSigma : IsSigmaCompact Gamma)
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hContact : Gamma ⊆ distanceContactSet u) :
    Euclidean n -> Euclidean n :=
  Classical.choose
    (existsMeasurableSegmentwiseLipschitzDirectionField
      hSigma hDiagonal
        (distanceContactSubsetNoCrossing u hu hContact))

/-- The selected direction field is measurable, agrees with every generating
segment, and is zero-Lipschitz along each such segment. -/
theorem contactSetDirectionField_spec {n : Nat}
    (u : Euclidean n -> Real)
    (hu : LipschitzWith 1 u)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hSigma : IsSigmaCompact Gamma)
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hContact : Gamma ⊆ distanceContactSet u) :
    Measurable
        (contactSetDirectionField
          u hu Gamma hSigma hDiagonal hContact) /\
      (∀ z ∈ transportSet Gamma,
        ∀ x y, (x, y) ∈ Gamma ->
          z ∈ openSegment Real x y ->
            contactSetDirectionField
              u hu Gamma hSigma hDiagonal hContact z =
                rayDirection x y) /\
      ∀ x y, (x, y) ∈ Gamma ->
        LipschitzOnWith 0
          (contactSetDirectionField
            u hu Gamma hSigma hDiagonal hContact)
          (openSegment Real x y) :=
  Classical.choose_spec
    (existsMeasurableSegmentwiseLipschitzDirectionField
      hSigma hDiagonal
        (distanceContactSubsetNoCrossing u hu hContact))

/-- The exact compact-exhaustion upgrade still missing after selecting the
measurable segmentwise direction field. Segmentwise constancy alone does not
give a common Lipschitz bound across a compact family of different rays. -/
def ContactDirectionCompactExhaustionPremise {n : Nat}
    (rho : Measure (Euclidean n))
    (u : Euclidean n -> Real)
    (hu : LipschitzWith 1 u)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hSigma : IsSigmaCompact Gamma)
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hContact : Gamma ⊆ distanceContactSet u) : Prop :=
  Nonempty
    (RayDirectionCompactExhaustion rho Gamma
      (contactSetDirectionField
        u hu Gamma hSigma hDiagonal hContact))

/-- The canonical contact direction has an increasing compact exhaustion on
which it is Lipschitz. The exhaustion covers the whole transport set, so its
exceptional set is empty. -/
theorem contactDirectionCompactExhaustionPremise
    {n : Nat}
    (rho : Measure (Euclidean n))
    (u : Euclidean n -> Real)
    (hu : LipschitzWith 1 u)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hSigma : IsSigmaCompact Gamma)
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hContact : Gamma ⊆ distanceContactSet u) :
    ContactDirectionCompactExhaustionPremise
      rho u hu Gamma hSigma hDiagonal hContact := by
  let directionField :=
    contactSetDirectionField
      u hu Gamma hSigma hDiagonal hContact
  have hDirectionAgrees :
      ∀ z ∈ transportSet Gamma,
        ∀ x y, (x, y) ∈ Gamma ->
          z ∈ openSegment Real x y ->
            directionField z = rayDirection x y :=
    (contactSetDirectionField_spec
      u hu Gamma hSigma hDiagonal hContact).2.1
  obtain
      ⟨compactPiece, hMonotone, hCompact, hCover, hLipschitz⟩ :=
    existsContactDirectionCompactExhaustion
      u hu hSigma hContact directionField hDirectionAgrees
  refine ⟨{
    exceptional := ∅
    exceptionalNegligible := by simp
    exceptionalSubset := empty_subset _
    compactPiece := compactPiece
    compactPieceMonotone := hMonotone
    compactPieceIsCompact := hCompact
    compactPieceCover := ?_
    directionLipschitz := hLipschitz
  }⟩
  simpa using hCover

/-- The no-crossing and oriented saturation parts of the target follow from
the pinned distance-contact geometry alone. -/
theorem contactSetNoCrossingAndRaySaturation
    {n : Nat}
    (u : Euclidean n -> Real)
    (hu : LipschitzWith 1 u)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hContact : Gamma ⊆ distanceContactSet u) :
    NoCrossing Gamma /\
      ∀ R : OrientedOpenRay n,
        R.IsMaximalTransportRay Gamma ->
          ∀ x ∈ R.carrier, ∀ y ∈ R.carrier,
            OrientedBefore R x y ->
              u x - u y = dist x y := by
  have hNoCrossing : NoCrossing Gamma :=
    distanceContactSubsetNoCrossing u hu hContact
  refine ⟨hNoCrossing, ?_⟩
  intro R hMaximal x hx y hy hBefore
  exact
    distanceContactCoveredRaySaturation
      u hu hContact R hMaximal.1 hx hy hBefore

/-- Assemble the regularity package once endpoint-nullity and the compact
countably-Lipschitz exhaustion have been supplied. -/
def rayRegularityHypothesesOfCompactExhaustion
    {n : Nat}
    {rho : Measure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (hNoCrossing : NoCrossing Gamma)
    (directionField : Euclidean n -> Euclidean n)
    (hDirectionAgrees :
      ∀ z ∈ transportSet Gamma,
        ∀ x y, (x, y) ∈ Gamma ->
          z ∈ openSegment Real x y ->
            directionField z = rayDirection x y)
    (hLeftEndpoint :
      rho (leftTransportSet Gamma \ transportSet Gamma) = 0)
    (hExhaustion :
      RayDirectionCompactExhaustion rho Gamma directionField) :
    RayRegularityHypotheses rho Gamma where
  noCrossing := hNoCrossing
  directionField := directionField
  directionAgrees := hDirectionAgrees
  leftEndpointNegligible := hLeftEndpoint
  exceptional := hExhaustion.exceptional
  exceptionalNegligible := hExhaustion.exceptionalNegligible
  exceptionalSubset := hExhaustion.exceptionalSubset
  compactPiece := hExhaustion.compactPiece
  compactPieceMonotone := hExhaustion.compactPieceMonotone
  compactPieceIsCompact := hExhaustion.compactPieceIsCompact
  compactPieceCover := hExhaustion.compactPieceCover
  directionLipschitz := hExhaustion.directionLipschitz

/-- Conditional closure of the target from exactly the two
measure-theoretic inputs not supplied by the current pinned contact modules:
left-endpoint nullity and the compact countably-Lipschitz exhaustion. -/
theorem contactSetRayRegularityOfEndpointAndCompactExhaustion
    (n : Nat)
    (u : Euclidean n -> Real)
    (hu : LipschitzWith 1 u)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hSigma : IsSigmaCompact Gamma)
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hContact : Gamma ⊆ distanceContactSet u)
    (hLeftEndpoint :
      (volume : Measure (Euclidean n))
        (leftTransportSet Gamma \ transportSet Gamma) = 0)
    (hCompactExhaustion :
      ContactDirectionCompactExhaustionPremise
        (volume : Measure (Euclidean n))
        u hu Gamma hSigma hDiagonal hContact) :
    NoCrossing Gamma /\
      (∀ R : OrientedOpenRay n,
        R.IsMaximalTransportRay Gamma ->
          ∀ x ∈ R.carrier, ∀ y ∈ R.carrier,
            OrientedBefore R x y ->
              u x - u y = dist x y) /\
      Nonempty
        (RayRegularityHypotheses
          (volume : Measure (Euclidean n)) Gamma) := by
  obtain ⟨hNoCrossing, hSaturation⟩ :=
    contactSetNoCrossingAndRaySaturation u hu Gamma hContact
  have hDirectionAgrees :=
    (contactSetDirectionField_spec
      u hu Gamma hSigma hDiagonal hContact).2.1
  obtain ⟨hExhaustion⟩ := hCompactExhaustion
  refine ⟨hNoCrossing, hSaturation, ?_⟩
  exact
    ⟨rayRegularityHypothesesOfCompactExhaustion
      hNoCrossing
      (contactSetDirectionField
        u hu Gamma hSigma hDiagonal hContact)
      hDirectionAgrees
      hLeftEndpoint hExhaustion⟩

/-- The contact-set regularity package now reduces to left-endpoint
negligibility alone; the compact direction exhaustion is unconditional. -/
theorem contactSetRayRegularityOfEndpoint
    (n : Nat)
    (u : Euclidean n -> Real)
    (hu : LipschitzWith 1 u)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hSigma : IsSigmaCompact Gamma)
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hContact : Gamma ⊆ distanceContactSet u)
    (hLeftEndpoint :
      (volume : Measure (Euclidean n))
        (leftTransportSet Gamma \ transportSet Gamma) = 0) :
    NoCrossing Gamma /\
      (∀ R : OrientedOpenRay n,
        R.IsMaximalTransportRay Gamma ->
          ∀ x ∈ R.carrier, ∀ y ∈ R.carrier,
            OrientedBefore R x y ->
              u x - u y = dist x y) /\
      Nonempty
        (RayRegularityHypotheses
          (volume : Measure (Euclidean n)) Gamma) := by
  exact
    contactSetRayRegularityOfEndpointAndCompactExhaustion
      n u hu Gamma hSigma hDiagonal hContact hLeftEndpoint
      (contactDirectionCompactExhaustionPremise
        (volume : Measure (Euclidean n))
        u hu Gamma hSigma hDiagonal hContact)

/-- Paper Theorem 3: sigma-compact diagonal-free subsets of a distance
contact set have the no-crossing, saturation, endpoint-nullity, and
countably-Lipschitz direction properties needed for ray disintegration. -/
theorem contactSetRayRegularity
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (u : Euclidean n -> Real)
    (hu : LipschitzWith 1 u)
    (Gamma : Set (Euclidean n × Euclidean n))
    (hSigma : IsSigmaCompact Gamma)
    (hDiagonal : ∀ x, (x, x) ∉ Gamma)
    (hContact : Gamma ⊆ distanceContactSet u) :
    NoCrossing Gamma /\
      (∀ R : OrientedOpenRay n,
        R.IsMaximalTransportRay Gamma ->
          ∀ x ∈ R.carrier, ∀ y ∈ R.carrier,
            OrientedBefore R x y ->
              u x - u y = dist x y) /\
      Nonempty
        (RayRegularityHypotheses
          (volume : Measure (Euclidean n)) Gamma) := by
  exact
    contactSetRayRegularityOfEndpoint
      n u hu Gamma hSigma hDiagonal hContact
      (contactLeftEndpointNegligible u hu Gamma hSigma hContact)

end ConcaveOTLimit

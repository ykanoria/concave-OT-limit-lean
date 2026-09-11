import Theorems.Thm_ConcaveOTLimit_canonicalRaywiseReplacementIntegration
import Theorems.Thm_ConcaveOTLimit_contactSetRayRegularity
import Theorems.Thm_ConcaveOTLimit_distanceContactCharacterization
import Theorems.Thm_ConcaveOTLimit_finiteCouplingAvoidsDiagonalOfMutuallySingular

open MeasureTheory Set

noncomputable section

namespace ConcaveOTLimit

private theorem isSigmaCompact_inter_isOpen
    {X : Type*} [PseudoEMetricSpace X]
    {s t : Set X}
    (hs : IsSigmaCompact s) (ht : IsOpen t) :
    IsSigmaCompact (s ∩ t) := by
  obtain ⟨K, hK, hKs⟩ := hs
  obtain ⟨F, hFclosed, _hFsub, hFt, _hFmono⟩ :=
    ht.exists_iUnion_isClosed
  have hCover : s ∩ t = ⋃ i, ⋃ j, K i ∩ F j := by
    rw [← hKs, ← hFt]
    ext x
    simp only [mem_inter_iff, mem_iUnion]
    constructor
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      exact ⟨i, j, hi, hj⟩
    · rintro ⟨i, j, hi, hj⟩
      exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  rw [hCover]
  exact isSigmaCompact_iUnion _ fun i =>
    isSigmaCompact_iUnion _ fun j =>
      ((hK i).inter_right (hFclosed j)).isSigmaCompact

private theorem distanceContactCharacterization_of_distanceDualWitness_zero
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (w : DistanceDualWitness mu nu) :
    exists u : Euclidean n -> Real,
      LipschitzWith 1 u /\
        (∀ gamma : FiniteCoupling mu nu,
          IsDistanceOptimal gamma <->
            IsSupported gamma (distanceContactSet u)) /\
        IsDistanceCyclicallyMonotone.{0, 0}
          (distanceContactSet u) :=
  distanceContactCharacterization_of_distanceDualWitness
    n mu nu hMarginals.sourceFirstMoment hMarginals.targetFirstMoment w

/-- The potential selected from the conditional distance-contact
characterization. -/
noncomputable def uniqueSecondaryDistancePotential
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (w : DistanceDualWitness mu nu) :
    Euclidean n -> Real :=
  Classical.choose
    (distanceContactCharacterization_of_distanceDualWitness_zero
      n mu nu hMarginals w)

theorem uniqueSecondaryDistancePotential_spec
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (w : DistanceDualWitness mu nu) :
    LipschitzWith 1
        (uniqueSecondaryDistancePotential n mu nu hMarginals w) /\
      (∀ gamma : FiniteCoupling mu nu,
        IsDistanceOptimal gamma <->
          IsSupported gamma
            (distanceContactSet
              (uniqueSecondaryDistancePotential n mu nu hMarginals w))) /\
      IsDistanceCyclicallyMonotone.{0, 0}
        (distanceContactSet
          (uniqueSecondaryDistancePotential n mu nu hMarginals w)) :=
  Classical.choose_spec
    (distanceContactCharacterization_of_distanceDualWitness_zero
      n mu nu hMarginals w)

/-- The full distance-contact set with the diagonal removed. -/
def uniqueSecondaryContactSet
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (w : DistanceDualWitness mu nu) :
    Set (Euclidean n × Euclidean n) :=
  distanceContactSet
      (uniqueSecondaryDistancePotential n mu nu hMarginals w) \
    {z : Euclidean n × Euclidean n | z.1 = z.2}

theorem uniqueSecondaryContactSet_diagonalFree
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (w : DistanceDualWitness mu nu) :
    ∀ x, (x, x) ∉
      uniqueSecondaryContactSet n mu nu hMarginals w := by
  intro x hx
  exact hx.2 rfl

theorem uniqueSecondaryContactSet_subset
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (w : DistanceDualWitness mu nu) :
    uniqueSecondaryContactSet n mu nu hMarginals w ⊆
      distanceContactSet
        (uniqueSecondaryDistancePotential n mu nu hMarginals w) :=
  fun _ hz => hz.1

theorem uniqueSecondaryContactSet_isSigmaCompact
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (w : DistanceDualWitness mu nu) :
    IsSigmaCompact
      (uniqueSecondaryContactSet n mu nu hMarginals w) := by
  let u := uniqueSecondaryDistancePotential n mu nu hMarginals w
  have hu : LipschitzWith 1 u := by
    simpa only [u] using
      (uniqueSecondaryDistancePotential_spec n mu nu hMarginals w).1
  have hContactClosed : IsClosed (distanceContactSet u) := by
    apply isClosed_eq
    · fun_prop
    · exact
        (hu.continuous.comp continuous_fst).sub
          (hu.continuous.comp continuous_snd)
  have hContactSigma : IsSigmaCompact (distanceContactSet u) :=
    IsSigmaCompact.of_isClosed_subset
      isSigmaCompact_univ hContactClosed (subset_univ _)
  have hOffDiagonalOpen :
      IsOpen
        {z : Euclidean n × Euclidean n | z.1 ≠ z.2} :=
    isOpen_ne_fun continuous_fst continuous_snd
  change
    IsSigmaCompact
      (distanceContactSet u ∩
        {z : Euclidean n × Euclidean n | z.1 ≠ z.2})
  exact isSigmaCompact_inter_isOpen hContactSigma hOffDiagonalOpen

/-- Mutual singularity makes support on a set equivalent to support on that
set with the diagonal removed. -/
theorem isSupported_diagonalRemoved_iff
    {X : Type*} [MeasurableSpace X]
    {mu nu : FiniteMeasure X}
    (gamma : FiniteCoupling mu nu)
    (hSingular : FiniteMutuallySingular mu nu)
    (S : Set (X × X)) :
    IsSupported gamma
        (S \ {z : X × X | z.1 = z.2}) <->
      IsSupported gamma S := by
  constructor
  · intro hSupported
    filter_upwards [hSupported] with z hz
    exact hz.1
  · intro hSupported
    have hOffDiagonal :=
      finiteCouplingAvoidsDiagonalOfMutuallySingular gamma hSingular
    filter_upwards [hSupported, hOffDiagonal] with z hz hne
    exact ⟨hz, hne⟩

/-- The source-measure regularity package obtained from the two external
contact-ray regularity producers. -/
noncomputable def uniqueSecondaryRayRegularity
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (w : DistanceDualWitness mu nu)
    (hLeftEndpoint :
      (volume : Measure (Euclidean n))
        (leftTransportSet
            (uniqueSecondaryContactSet n mu nu hMarginals w) \
          transportSet
            (uniqueSecondaryContactSet n mu nu hMarginals w)) = 0)
    (hCompactExhaustion :
      ContactDirectionCompactExhaustionPremise
        (volume : Measure (Euclidean n))
        (uniqueSecondaryDistancePotential n mu nu hMarginals w)
        (uniqueSecondaryDistancePotential_spec n mu nu hMarginals w).1
        (uniqueSecondaryContactSet n mu nu hMarginals w)
        (uniqueSecondaryContactSet_isSigmaCompact
          n mu nu hMarginals w)
        (uniqueSecondaryContactSet_diagonalFree
          n mu nu hMarginals w)
        (uniqueSecondaryContactSet_subset
          n mu nu hMarginals w)) :
    RayRegularityHypotheses
      (mu : Measure (Euclidean n))
      (uniqueSecondaryContactSet n mu nu hMarginals w) :=
  RayRegularityHypotheses.of_absolutelyContinuous
    (Classical.choice
      (contactSetRayRegularityOfEndpointAndCompactExhaustion
        n
        (uniqueSecondaryDistancePotential n mu nu hMarginals w)
        (uniqueSecondaryDistancePotential_spec n mu nu hMarginals w).1
        (uniqueSecondaryContactSet n mu nu hMarginals w)
        (uniqueSecondaryContactSet_isSigmaCompact
          n mu nu hMarginals w)
        (uniqueSecondaryContactSet_diagonalFree
          n mu nu hMarginals w)
        (uniqueSecondaryContactSet_subset
          n mu nu hMarginals w)
        hLeftEndpoint hCompactExhaustion).2.2)
    hMarginals.sourceAbsolutelyContinuous

/-- Exactly the external producers left at the final assembly boundary. -/
structure UniqueSecondaryMinimizerAssemblyPremise
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu) where
  distanceDualWitness : DistanceDualWitness mu nu
  leftEndpointNegligible :
    (volume : Measure (Euclidean n))
      (leftTransportSet
          (uniqueSecondaryContactSet
            n mu nu hMarginals distanceDualWitness) \
        transportSet
          (uniqueSecondaryContactSet
            n mu nu hMarginals distanceDualWitness)) = 0
  compactExhaustion :
    ContactDirectionCompactExhaustionPremise
      (volume : Measure (Euclidean n))
      (uniqueSecondaryDistancePotential
        n mu nu hMarginals distanceDualWitness)
      (uniqueSecondaryDistancePotential_spec
        n mu nu hMarginals distanceDualWitness).1
      (uniqueSecondaryContactSet
        n mu nu hMarginals distanceDualWitness)
      (uniqueSecondaryContactSet_isSigmaCompact
        n mu nu hMarginals distanceDualWitness)
      (uniqueSecondaryContactSet_diagonalFree
        n mu nu hMarginals distanceDualWitness)
      (uniqueSecondaryContactSet_subset
        n mu nu hMarginals distanceDualWitness)
  canonicalRaywisePremise :
    CanonicalRaywiseReplacementIntegrationPremise
      n mu nu
      (uniqueSecondaryContactSet
        n mu nu hMarginals distanceDualWitness)
      (uniqueSecondaryRayRegularity
        n mu nu hMarginals distanceDualWitness
        leftEndpointNegligible compactExhaustion)

/-- Conditional final assembly of the exact `uniqueSecondaryMinimizer`
conclusion. -/
theorem uniqueSecondaryMinimizer_of_assemblyPremise
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (hAssembly :
      UniqueSecondaryMinimizerAssemblyPremise
        n mu nu hMarginals) :
    exists gammaSharp : FiniteCoupling mu nu,
      exists tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
          IsIntrinsicGeneralizedECPlan mu nu gammaSharp /\
          exists u : Euclidean n -> Real,
            LipschitzWith 1 u /\
              exists Gamma : Set (Euclidean n × Euclidean n),
                Gamma =
                  distanceContactSet u \
                    {z : Euclidean n × Euclidean n | z.1 = z.2} /\
                IsSigmaCompact Gamma /\
                Nonempty
                  (RaywiseExcursionDisintegration
                    Gamma mu nu gammaSharp.plan tSharp) := by
  let w := hAssembly.distanceDualWitness
  let u := uniqueSecondaryDistancePotential n mu nu hMarginals w
  let Gamma := uniqueSecondaryContactSet n mu nu hMarginals w
  let hRegularity :=
    uniqueSecondaryRayRegularity
      n mu nu hMarginals hAssembly.distanceDualWitness
      hAssembly.leftEndpointNegligible hAssembly.compactExhaustion
  have hu : LipschitzWith 1 u := by
    simpa only [u, w] using
      (uniqueSecondaryDistancePotential_spec
        n mu nu hMarginals hAssembly.distanceDualWitness).1
  have hContactCharacterization :
      ∀ gamma : FiniteCoupling mu nu,
        IsDistanceOptimal gamma <->
          IsSupported gamma (distanceContactSet u) := by
    simpa only [u, w] using
      (uniqueSecondaryDistancePotential_spec
        n mu nu hMarginals hAssembly.distanceDualWitness).2.1
  have hContactCyclic :
      IsDistanceCyclicallyMonotone.{0, 0}
        (distanceContactSet u) := by
    intro I _ x y hxy sigma
    exact
      (uniqueSecondaryDistancePotential_spec
        n mu nu hMarginals hAssembly.distanceDualWitness).2.2
          x y (by simpa only [u, w] using hxy) sigma
  have hSigma : IsSigmaCompact Gamma := by
    simpa only [Gamma, w] using
      uniqueSecondaryContactSet_isSigmaCompact
        n mu nu hMarginals hAssembly.distanceDualWitness
  have hDiagonal : ∀ x, (x, x) ∉ Gamma := by
    simpa only [Gamma, w] using
      uniqueSecondaryContactSet_diagonalFree
        n mu nu hMarginals hAssembly.distanceDualWitness
  have hGammaSubset : Gamma ⊆ distanceContactSet u := by
    simpa only [Gamma, u, w] using
      uniqueSecondaryContactSet_subset
        n mu nu hMarginals hAssembly.distanceDualWitness
  have hGammaCyclic :
      IsDistanceCyclicallyMonotone.{0, 0} Gamma := by
    intro I _ x y hxy sigma
    exact hContactCyclic x y (fun i => hGammaSubset (hxy i)) sigma
  obtain ⟨gamma0, hGamma0Cost⟩ :=
    hAssembly.distanceDualWitness.minimum.1
  have hGamma0Optimal : IsDistanceOptimal gamma0 :=
    (hAssembly.distanceDualWitness.isDistanceOptimal_iff_distanceCost_eq
      gamma0).2 hGamma0Cost
  have hGamma0Contact :
      IsSupported gamma0 (distanceContactSet u) :=
    (hContactCharacterization gamma0).1 hGamma0Optimal
  have hGamma0Supported : IsSupported gamma0 Gamma := by
    simpa only [Gamma, uniqueSecondaryContactSet, u, w] using
      ((isSupported_diagonalRemoved_iff
        gamma0 hMarginals.mutuallySingular
        (distanceContactSet u)).2 hGamma0Contact)
  have hCanonicalPremise :
      CanonicalRaywiseReplacementIntegrationPremise
        n mu nu Gamma hRegularity := by
    simpa only [Gamma, hRegularity, w] using
      hAssembly.canonicalRaywisePremise
  obtain
      ⟨gammaSharp, tSharp, hGraph, hCyclicOptimal, _hSameRay,
        hDisintegration, hComparison⟩ :=
    canonicalRaywiseReplacement_of_integrationPremise_and_optimalInput
      n mu nu hMarginals Gamma hSigma hDiagonal hRegularity
      gamma0 hGamma0Supported hGamma0Optimal hCanonicalPremise
  have hGammaSharpOptimal : IsDistanceOptimal gammaSharp :=
    hCyclicOptimal hGammaCyclic
  have hSupportedGammaOfOptimal :
      ∀ eta : FiniteCoupling mu nu,
        IsDistanceOptimal eta -> IsSupported eta Gamma := by
    intro eta hEtaOptimal
    have hEtaContact :
        IsSupported eta (distanceContactSet u) :=
      (hContactCharacterization eta).1 hEtaOptimal
    simpa only [Gamma, uniqueSecondaryContactSet, u, w] using
      ((isSupported_diagonalRemoved_iff
        eta hMarginals.mutuallySingular
        (distanceContactSet u)).2 hEtaContact)
  have hIntrinsic :
      IsIntrinsicGeneralizedECPlan mu nu gammaSharp := by
    intro profile hStrict
    have hConcave : AdmissibleConcaveProfile profile :=
      ⟨hStrict.1.concaveOn, hStrict.2⟩
    refine ⟨⟨hGammaSharpOptimal, ?_⟩, ?_⟩
    · intro eta hEtaOptimal
      exact
        (hComparison eta
          (hSupportedGammaOfOptimal eta hEtaOptimal)
          profile hConcave).1
    · intro eta hEtaMinimizer
      have hEtaOptimal : IsDistanceOptimal eta :=
        hEtaMinimizer.1
      have hEtaSupported : IsSupported eta Gamma :=
        hSupportedGammaOfOptimal eta hEtaOptimal
      have hSharpLeEta :
          profileCost profile gammaSharp <= profileCost profile eta :=
        (hComparison eta hEtaSupported profile hConcave).1
      have hEtaLeSharp :
          profileCost profile eta <= profileCost profile gammaSharp :=
        hEtaMinimizer.2 gammaSharp hGammaSharpOptimal
      exact
        ((hComparison eta hEtaSupported profile hConcave).2 hStrict).1
          (le_antisymm hSharpLeEta hEtaLeSharp)
  refine
    ⟨gammaSharp, tSharp, hGraph, hIntrinsic, u, hu, Gamma, ?_,
      hSigma, hDisintegration⟩
  rfl

#print axioms uniqueSecondaryMinimizer_of_assemblyPremise

end ConcaveOTLimit

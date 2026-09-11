import Theorems.Thm_ConcaveOTLimit_canonicalRaywiseReplacementAssembly
import Theorems.Thm_ConcaveOTLimit_contactSetRayRegularity
import Theorems.Thm_ConcaveOTLimit_distanceContactCharacterization
import Theorems.Thm_ConcaveOTLimit_finiteCouplingAvoidsDiagonalOfMutuallySingular
import Theorems.Thm_ConcaveOTLimit_logarithmicCostIntegrableOfMarginalLogMoments
import Mathlib.Tactic.Linarith

open MeasureTheory Set

noncomputable section

namespace ConcaveOTLimit

private theorem psi_nonnegative {r : Real} (hr : 0 <= r) :
    0 <= Psi r := by
  exact mul_nonneg hr (Real.log_nonneg (by linarith))

private theorem le_one_add_psi {r : Real} (hr : 0 <= r) :
    r <= 1 + Psi r := by
  by_cases hrOne : r <= 1
  · linarith [psi_nonnegative hr]
  · have hrPos : 0 < r :=
      lt_of_lt_of_le zero_lt_one (le_of_not_ge hrOne)
    have hLog :=
      Real.one_sub_inv_le_log_of_pos (show 0 < 1 + r by linarith)
    have hMul :
        r * (1 - (1 + r)⁻¹) <= r * Real.log (1 + r) :=
      mul_le_mul_of_nonneg_left hLog hr
    have hFraction : r / (1 + r) <= 1 :=
      (div_le_one (by linarith)).2 (by linarith)
    rw [mul_sub, mul_one] at hMul
    rw [div_eq_mul_inv] at hFraction
    unfold Psi
    linarith

/-- A logarithmic Orlicz moment implies the first moment needed by the
fixed-contact raywise assembly. -/
theorem integrableNormOfIntegrablePsiNorm
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
    {rho : Measure E} [IsFiniteMeasure rho]
    (hPsi : Integrable (fun x : E => Psi ‖x‖) rho) :
    Integrable (fun x : E => ‖x‖) rho := by
  have hBound :
      Integrable (fun x : E => 1 + Psi ‖x‖) rho :=
    (integrable_const 1).add hPsi
  refine hBound.mono' continuous_norm.aestronglyMeasurable ?_
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)] using
    le_one_add_psi (norm_nonneg x)

/-- The power hypotheses contain all ordinary marginal hypotheses after
using the Orlicz-to-first-moment estimate. -/
def marginalHypothesesOfPower
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu) :
    MarginalHypotheses n mu nu where
  equalMass := hPower.equalMass
  positiveMass := hPower.positiveMass
  mutuallySingular := hPower.mutuallySingular
  sourceAbsolutelyContinuous := hPower.sourceAbsolutelyContinuous
  sourceFirstMoment :=
    integrableNormOfIntegrablePsiNorm hPower.sourceLogMoment
  targetFirstMoment :=
    integrableNormOfIntegrablePsiNorm hPower.targetLogMoment

/-- The fixed distance-contact support used for both the admissible-profile
and logarithmic branches. -/
def logarithmicSecondaryContactSet
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    (w : DistanceDualWitness mu nu) :
    Set (Euclidean n × Euclidean n) :=
  distanceContactSet w.potential \
    {z : Euclidean n × Euclidean n | z.1 = z.2}

private theorem logarithmicSecondaryContactSet_diagonalFree
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    (w : DistanceDualWitness mu nu) :
    ∀ x, (x, x) ∉ logarithmicSecondaryContactSet w := by
  intro x hx
  exact hx.2 rfl

private theorem logarithmicSecondaryContactSet_subset
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    (w : DistanceDualWitness mu nu) :
    logarithmicSecondaryContactSet w ⊆
      distanceContactSet w.potential :=
  fun _ hz => hz.1

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

private theorem logarithmicSecondaryContactSet_isSigmaCompact
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    (w : DistanceDualWitness mu nu) :
    IsSigmaCompact (logarithmicSecondaryContactSet w) := by
  have hContactClosed : IsClosed (distanceContactSet w.potential) := by
    apply isClosed_eq
    · fun_prop
    · exact
        (w.lipschitz.continuous.comp continuous_fst).sub
          (w.lipschitz.continuous.comp continuous_snd)
  have hContactSigma :
      IsSigmaCompact (distanceContactSet w.potential) :=
    IsSigmaCompact.of_isClosed_subset
      isSigmaCompact_univ hContactClosed (subset_univ _)
  have hOffDiagonalOpen :
      IsOpen {z : Euclidean n × Euclidean n | z.1 ≠ z.2} :=
    isOpen_ne_fun continuous_fst continuous_snd
  change
    IsSigmaCompact
      (distanceContactSet w.potential ∩
        {z : Euclidean n × Euclidean n | z.1 ≠ z.2})
  exact isSigmaCompact_inter_isOpen hContactSigma hOffDiagonalOpen

private theorem isSupported_diagonalRemoved_iff
    {X : Type*} [MeasurableSpace X]
    {mu nu : FiniteMeasure X}
    (gamma : FiniteCoupling mu nu)
    (hSingular : FiniteMutuallySingular mu nu)
    (S : Set (X × X)) :
    IsSupported gamma (S \ {z : X × X | z.1 = z.2}) <->
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

/-- The source-measure ray regularity obtained from the two non-logarithmic
contact-ray producers. -/
noncomputable def logarithmicSecondaryRayRegularity
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (w : DistanceDualWitness mu nu)
    (hLeftEndpoint :
      (volume : Measure (Euclidean n))
        (leftTransportSet (logarithmicSecondaryContactSet w) \
          transportSet (logarithmicSecondaryContactSet w)) = 0)
    (hCompactExhaustion :
      ContactDirectionCompactExhaustionPremise
        (volume : Measure (Euclidean n))
        w.potential w.lipschitz
        (logarithmicSecondaryContactSet w)
        (logarithmicSecondaryContactSet_isSigmaCompact w)
        (logarithmicSecondaryContactSet_diagonalFree w)
        (logarithmicSecondaryContactSet_subset w)) :
    RayRegularityHypotheses
      (mu : Measure (Euclidean n))
      (logarithmicSecondaryContactSet w) :=
  RayRegularityHypotheses.of_absolutelyContinuous
    (Classical.choice
      (contactSetRayRegularityOfEndpointAndCompactExhaustion
        n w.potential w.lipschitz
        (logarithmicSecondaryContactSet w)
        (logarithmicSecondaryContactSet_isSigmaCompact w)
        (logarithmicSecondaryContactSet_diagonalFree w)
        (logarithmicSecondaryContactSet_subset w)
        hLeftEndpoint hCompactExhaustion).2.2)
    hMarginals.sourceAbsolutelyContinuous

/-- The exact logarithmic input left after fixed-marginal integrability,
contact support, coordinate inheritance, and Juillet identification are
available. It asks for the integrated raywise comparison and equality
rigidity only when both logarithmic costs are known to be integrable. -/
def LogarithmicRaywiseComparisonOfIntegrablePremise
    {n : Nat} {mu nu : FiniteMeasure (Euclidean n)}
    (Gamma : Set (Euclidean n × Euclidean n)) : Prop :=
  ∀ (gammaSharp : FiniteCoupling mu nu)
    (tSharp : Euclidean n -> Euclidean n),
    Nonempty
        (RaywiseExcursionDisintegration
          Gamma mu nu gammaSharp.plan tSharp) ->
      IsSupported gammaSharp Gamma ->
        ∀ eta : FiniteCoupling mu nu,
          IsSupported eta Gamma ->
            Integrable
                (fun z : Euclidean n × Euclidean n =>
                  logarithmicProfile ‖z.1 - z.2‖)
                (gammaSharp.plan :
                  Measure (Euclidean n × Euclidean n)) ->
              Integrable
                  (fun z : Euclidean n × Euclidean n =>
                    logarithmicProfile ‖z.1 - z.2‖)
                  (eta.plan :
                    Measure (Euclidean n × Euclidean n)) ->
                profileCost logarithmicProfile gammaSharp <=
                    profileCost logarithmicProfile eta /\
                  (profileCost logarithmicProfile gammaSharp =
                      profileCost logarithmicProfile eta ->
                    eta = gammaSharp)

/-- All non-logarithmic fields are the existing fixed-contact raywise
assembly boundary. The final field is the sole additional producer needed
for the logarithmic profile. -/
structure LogarithmicSecondaryUniquenessAssemblyPremise
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu) where
  distanceDualWitness : DistanceDualWitness mu nu
  leftEndpointNegligible :
    (volume : Measure (Euclidean n))
      (leftTransportSet
          (logarithmicSecondaryContactSet distanceDualWitness) \
        transportSet
          (logarithmicSecondaryContactSet distanceDualWitness)) = 0
  compactExhaustion :
    ContactDirectionCompactExhaustionPremise
      (volume : Measure (Euclidean n))
      distanceDualWitness.potential
      distanceDualWitness.lipschitz
      (logarithmicSecondaryContactSet distanceDualWitness)
      (logarithmicSecondaryContactSet_isSigmaCompact
        distanceDualWitness)
      (logarithmicSecondaryContactSet_diagonalFree
        distanceDualWitness)
      (logarithmicSecondaryContactSet_subset distanceDualWitness)
  canonicalRaywiseAssembly :
    CanonicalRaywiseReplacementAssemblyPremise
      n mu nu
      (logarithmicSecondaryContactSet distanceDualWitness)
      (logarithmicSecondaryRayRegularity
        n mu nu
        (marginalHypothesesOfPower n mu nu hPower)
        distanceDualWitness leftEndpointNegligible compactExhaustion)
  logarithmicRaywiseComparison :
    LogarithmicRaywiseComparisonOfIntegrablePremise
      (n := n) (mu := mu) (nu := nu)
      (logarithmicSecondaryContactSet distanceDualWitness)

/-- Conditional assembly of the exact `logarithmicSecondaryUniqueness`
target. The logarithmic profile is never treated as globally admissible:
`Psi` moments supply integrability, and the final premise supplies only the
raywise logarithmic comparison and rigidity. -/
theorem logarithmicSecondaryUniqueness_of_assemblyPremise
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hPower : PowerMarginalHypotheses n mu nu)
    (hAssembly :
      LogarithmicSecondaryUniquenessAssemblyPremise
        n mu nu hPower) :
    exists gammaSharp : FiniteCoupling mu nu,
      exists tSharp : Euclidean n -> Euclidean n,
        IsGraphPlan gammaSharp tSharp /\
          IsIntrinsicGeneralizedECPlan mu nu gammaSharp /\
          IsUniqueSecondaryMinimizer
            logarithmicProfile gammaSharp := by
  let hMarginals := marginalHypothesesOfPower n mu nu hPower
  let w := hAssembly.distanceDualWitness
  let Gamma := logarithmicSecondaryContactSet w
  let hRegularity :=
    logarithmicSecondaryRayRegularity
      n mu nu hMarginals w
      hAssembly.leftEndpointNegligible hAssembly.compactExhaustion
  have hContactCharacterization :
      ∀ gamma : FiniteCoupling mu nu,
        IsDistanceOptimal gamma <->
          IsSupported gamma (distanceContactSet w.potential) := by
    intro gamma
    exact w.isDistanceOptimal_iff_isSupported
      hMarginals.sourceFirstMoment hMarginals.targetFirstMoment gamma
  have hContactCyclic :
      IsDistanceCyclicallyMonotone.{0, 0}
        (distanceContactSet w.potential) :=
    w.contactSetIsDistanceCyclicallyMonotone
  have hSigma : IsSigmaCompact Gamma := by
    simpa only [Gamma, w] using
      logarithmicSecondaryContactSet_isSigmaCompact
        hAssembly.distanceDualWitness
  have hDiagonal : ∀ x, (x, x) ∉ Gamma := by
    simpa only [Gamma, w] using
      logarithmicSecondaryContactSet_diagonalFree
        hAssembly.distanceDualWitness
  have hGammaSubset : Gamma ⊆ distanceContactSet w.potential := by
    simpa only [Gamma, w] using
      logarithmicSecondaryContactSet_subset
        hAssembly.distanceDualWitness
  have hGammaCyclic :
      IsDistanceCyclicallyMonotone.{0, 0} Gamma := by
    intro I _ x y hxy sigma
    exact hContactCyclic x y (fun i => hGammaSubset (hxy i)) sigma
  obtain ⟨gamma0, hGamma0Cost⟩ := w.minimum.1
  have hGamma0Optimal : IsDistanceOptimal gamma0 :=
    (w.isDistanceOptimal_iff_distanceCost_eq gamma0).2 hGamma0Cost
  have hGamma0Contact :
      IsSupported gamma0 (distanceContactSet w.potential) :=
    (hContactCharacterization gamma0).1 hGamma0Optimal
  have hGamma0Supported : IsSupported gamma0 Gamma := by
    change
      IsSupported gamma0
        (distanceContactSet w.potential \
          {z : Euclidean n × Euclidean n | z.1 = z.2})
    exact
      (isSupported_diagonalRemoved_iff
        gamma0 hMarginals.mutuallySingular
        (distanceContactSet w.potential)).2 hGamma0Contact
  have hCanonicalAssembly :
      CanonicalRaywiseReplacementAssemblyPremise
        n mu nu Gamma hRegularity := by
    simpa only [Gamma, hRegularity, w, hMarginals] using
      hAssembly.canonicalRaywiseAssembly
  obtain
      ⟨gammaSharp, tSharp, hGraph, hCyclicOptimal, _hSameRay,
        hDisintegration, hComparison⟩ :=
    canonicalRaywiseReplacement_of_assemblyPremise
      n mu nu hMarginals Gamma hSigma hDiagonal hRegularity
      ⟨gamma0, hGamma0Supported⟩ hCanonicalAssembly
  have hGammaSharpOptimal : IsDistanceOptimal gammaSharp :=
    hCyclicOptimal hGammaCyclic
  have hSupportedOfOptimal :
      ∀ eta : FiniteCoupling mu nu,
        IsDistanceOptimal eta -> IsSupported eta Gamma := by
    intro eta hEtaOptimal
    have hEtaContact :
        IsSupported eta (distanceContactSet w.potential) :=
      (hContactCharacterization eta).1 hEtaOptimal
    change
      IsSupported eta
        (distanceContactSet w.potential \
          {z : Euclidean n × Euclidean n | z.1 = z.2})
    exact
      (isSupported_diagonalRemoved_iff
        eta hMarginals.mutuallySingular
        (distanceContactSet w.potential)).2 hEtaContact
  have hGammaSharpSupported : IsSupported gammaSharp Gamma :=
    hSupportedOfOptimal gammaSharp hGammaSharpOptimal
  have hIntrinsic :
      IsIntrinsicGeneralizedECPlan mu nu gammaSharp := by
    intro profile hStrict
    have hConcave : AdmissibleConcaveProfile profile :=
      ⟨hStrict.1.concaveOn, hStrict.2⟩
    refine ⟨⟨hGammaSharpOptimal, ?_⟩, ?_⟩
    · intro eta hEtaOptimal
      exact
        (hComparison eta
          (hSupportedOfOptimal eta hEtaOptimal)
          profile hConcave).1
    · intro eta hEtaMinimizer
      have hEtaOptimal : IsDistanceOptimal eta :=
        hEtaMinimizer.1
      have hEtaSupported : IsSupported eta Gamma :=
        hSupportedOfOptimal eta hEtaOptimal
      have hSharpLeEta :
          profileCost profile gammaSharp <= profileCost profile eta :=
        (hComparison eta hEtaSupported profile hConcave).1
      have hEtaLeSharp :
          profileCost profile eta <= profileCost profile gammaSharp :=
        hEtaMinimizer.2 gammaSharp hGammaSharpOptimal
      exact
        ((hComparison eta hEtaSupported profile hConcave).2 hStrict).1
          (le_antisymm hSharpLeEta hEtaLeSharp)
  have hGammaSharpIntegrable :
      Integrable
        (fun z : Euclidean n × Euclidean n =>
          logarithmicProfile ‖z.1 - z.2‖)
        (gammaSharp.plan :
          Measure (Euclidean n × Euclidean n)) :=
    logarithmicCostIntegrableOfMarginalLogMoments
      hPower.sourceLogMoment hPower.targetLogMoment gammaSharp
  have hLogarithmicProducer :
      LogarithmicRaywiseComparisonOfIntegrablePremise
        (n := n) (mu := mu) (nu := nu) Gamma := by
    simpa only [Gamma, w] using
      hAssembly.logarithmicRaywiseComparison
  have hLogarithmicUnique :
      IsUniqueSecondaryMinimizer
        logarithmicProfile gammaSharp := by
    refine ⟨⟨hGammaSharpOptimal, ?_⟩, ?_⟩
    · intro eta hEtaOptimal
      have hEtaSupported : IsSupported eta Gamma :=
        hSupportedOfOptimal eta hEtaOptimal
      have hEtaIntegrable :
          Integrable
            (fun z : Euclidean n × Euclidean n =>
              logarithmicProfile ‖z.1 - z.2‖)
            (eta.plan : Measure (Euclidean n × Euclidean n)) :=
        logarithmicCostIntegrableOfMarginalLogMoments
          hPower.sourceLogMoment hPower.targetLogMoment eta
      exact
        (hLogarithmicProducer gammaSharp tSharp hDisintegration
          hGammaSharpSupported eta hEtaSupported
          hGammaSharpIntegrable hEtaIntegrable).1
    · intro eta hEtaMinimizer
      have hEtaOptimal : IsDistanceOptimal eta :=
        hEtaMinimizer.1
      have hEtaSupported : IsSupported eta Gamma :=
        hSupportedOfOptimal eta hEtaOptimal
      have hEtaIntegrable :
          Integrable
            (fun z : Euclidean n × Euclidean n =>
              logarithmicProfile ‖z.1 - z.2‖)
            (eta.plan : Measure (Euclidean n × Euclidean n)) :=
        logarithmicCostIntegrableOfMarginalLogMoments
          hPower.sourceLogMoment hPower.targetLogMoment eta
      have hLogarithmicComparison :=
        hLogarithmicProducer gammaSharp tSharp hDisintegration
          hGammaSharpSupported eta hEtaSupported
          hGammaSharpIntegrable hEtaIntegrable
      apply hLogarithmicComparison.2
      exact le_antisymm hLogarithmicComparison.1
        (hEtaMinimizer.2 gammaSharp hGammaSharpOptimal)
  exact
    ⟨gammaSharp, tSharp, hGraph, hIntrinsic, hLogarithmicUnique⟩

#print axioms logarithmicSecondaryUniqueness_of_assemblyPremise

end ConcaveOTLimit

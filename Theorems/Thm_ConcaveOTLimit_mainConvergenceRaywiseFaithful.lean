import Theorems.Thm_ConcaveOTLimit_mainConvergenceRaywise
import Theorems.Thm_ConcaveOTLimit_isGraphPlanMapUniqueAe
import Theorems.Thm_ConcaveOTLimit_positiveCrossingIndicatrixAtomless

open Filter MeasureTheory Set Topology

namespace ConcaveOTLimit

/-- The literal one-dimensional identification premise follows from the
atomless mutually-singular positive-crossing indicatrix theorem. -/
theorem literalJuilletIdentificationPremise_unconditional :
    LiteralJuilletIdentificationPremise := by
  apply literalJuilletIdentificationPremise_of_positiveCrossingIndicatrix
  intro mu nu hAtomless hSingular _hOrder
  exact
    positiveCrossingIndicatrixIdentity_of_atomless_mutuallySingular
      hAtomless hSingular

/-- Paper-faithful main convergence: the selected graph plan is intrinsically
optimal and disintegrates raywise into literal completed-graph excursion
couplings. -/
theorem mainConvergenceRaywise
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
  exact
    mainConvergenceRaywise_of_positiveCrossingIndicatrix
      (fun _ _ hAtomless hSingular _hOrder =>
        positiveCrossingIndicatrixIdentity_of_atomless_mutuallySingular
          hAtomless hSingular)
      n mu nu hMarginals

/-- Canonical form of `mainConvergenceRaywise`: the coupling is unique, and
every graph representative agrees source-almost everywhere with the selected
map. -/
theorem mainConvergenceRaywise_uniqueCoupling
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu) :
    ∃! gammaEC : FiniteCoupling mu nu,
      IsIntrinsicGeneralizedECPlan mu nu gammaEC /\
        ∃ tEC : Euclidean n -> Euclidean n,
          IsGraphPlan gammaEC tEC /\
            (∀ S, IsGraphPlan gammaEC S ->
              S =ᵐ[(mu : Measure (Euclidean n))] tEC) /\
            IsRaywiseGeneralizedECPlan mu nu gammaEC tEC /\
            ∀ family : Real -> Real -> Real,
              ∀ firstOrder : Real -> Real,
                PerturbationAssumptions family firstOrder ->
                  ∃ optimizers : OptimizerFamily mu nu family,
                    TendstoInMeasure
                      (mu : Measure (Euclidean n))
                      optimizers.transportMap
                      (nhdsWithin 0 epsilonDomain) tEC := by
  obtain
      ⟨gammaEC, tEC, hGraph, hIntrinsic, hRaywise, hConvergence⟩ :=
    mainConvergenceRaywise n mu nu hMarginals
  refine
    ⟨gammaEC,
      ⟨hIntrinsic, tEC, hGraph,
        fun _ hS => isGraphPlan_map_unique_ae hGraph hS,
        hRaywise, hConvergence⟩, ?_⟩
  intro eta hEta
  exact
    (hIntrinsic strictExponentialProfile
      strictExponentialProfile_admissible).2 eta
        ((hEta.1 strictExponentialProfile
          strictExponentialProfile_admissible).1)

/-- The unique coupling carrying the intrinsic, raywise, and convergence
conclusions of `mainConvergenceRaywise`. -/
noncomputable def canonicalGeneralizedECCoupling
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu) :
    FiniteCoupling mu nu :=
  Classical.choose
    (mainConvergenceRaywise_uniqueCoupling
      n mu nu hMarginals).exists

/-- The canonical generalized excursion coupling retains the complete
predicate from the unique-existence theorem. -/
theorem canonicalGeneralizedECCoupling_spec
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu) :
    IsIntrinsicGeneralizedECPlan mu nu
        (canonicalGeneralizedECCoupling n mu nu hMarginals) /\
      ∃ tEC : Euclidean n -> Euclidean n,
        IsGraphPlan
            (canonicalGeneralizedECCoupling n mu nu hMarginals) tEC /\
          (∀ S,
            IsGraphPlan
                (canonicalGeneralizedECCoupling n mu nu hMarginals) S ->
              S =ᵐ[(mu : Measure (Euclidean n))] tEC) /\
          IsRaywiseGeneralizedECPlan mu nu
              (canonicalGeneralizedECCoupling n mu nu hMarginals) tEC /\
          ∀ family : Real -> Real -> Real,
            ∀ firstOrder : Real -> Real,
              PerturbationAssumptions family firstOrder ->
                ∃ optimizers : OptimizerFamily mu nu family,
                  TendstoInMeasure
                    (mu : Measure (Euclidean n))
                    optimizers.transportMap
                    (nhdsWithin 0 epsilonDomain) tEC := by
  exact
    Classical.choose_spec
      (mainConvergenceRaywise_uniqueCoupling
        n mu nu hMarginals).exists

/-- A total representative of the canonical generalized excursion map. -/
noncomputable def canonicalGeneralizedECMap
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu) :
    Euclidean n -> Euclidean n :=
  Classical.choose
    (canonicalGeneralizedECCoupling_spec n mu nu hMarginals).2

/-- The canonical map represents the canonical coupling, is unique among its
graph representatives source-almost everywhere, satisfies the literal
raywise Juillet predicate, and is the limit of the complete optimizer
family. -/
theorem canonicalGeneralizedECMap_spec
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu) :
    IsGraphPlan
        (canonicalGeneralizedECCoupling n mu nu hMarginals)
        (canonicalGeneralizedECMap n mu nu hMarginals) /\
      (∀ S,
        IsGraphPlan
            (canonicalGeneralizedECCoupling n mu nu hMarginals) S ->
          S =ᵐ[(mu : Measure (Euclidean n))]
            canonicalGeneralizedECMap n mu nu hMarginals) /\
      IsRaywiseGeneralizedECPlan mu nu
          (canonicalGeneralizedECCoupling n mu nu hMarginals)
          (canonicalGeneralizedECMap n mu nu hMarginals) /\
      ∀ family : Real -> Real -> Real,
        ∀ firstOrder : Real -> Real,
          PerturbationAssumptions family firstOrder ->
            ∃ optimizers : OptimizerFamily mu nu family,
              TendstoInMeasure
                (mu : Measure (Euclidean n))
                optimizers.transportMap
                (nhdsWithin 0 epsilonDomain)
                (canonicalGeneralizedECMap n mu nu hMarginals) := by
  exact
    Classical.choose_spec
      (canonicalGeneralizedECCoupling_spec n mu nu hMarginals).2

/-- Every graph representative of the canonical coupling agrees with the
canonical map source-almost everywhere. -/
theorem canonicalGeneralizedECMap_unique_ae
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (S : Euclidean n -> Euclidean n)
    (hS : IsGraphPlan
      (canonicalGeneralizedECCoupling n mu nu hMarginals) S) :
    S =ᵐ[(mu : Measure (Euclidean n))]
      canonicalGeneralizedECMap n mu nu hMarginals :=
  (canonicalGeneralizedECMap_spec n mu nu hMarginals).2.1 S hS

/-- Intrinsic generalized excursion optimality characterizes the canonical
coupling. -/
theorem isIntrinsicGeneralizedECPlan_iff_eq_canonicalGeneralizedECCoupling
    (n : Nat)
    (mu nu : FiniteMeasure (Euclidean n))
    (hMarginals : MarginalHypotheses n mu nu)
    (gamma : FiniteCoupling mu nu) :
    IsIntrinsicGeneralizedECPlan mu nu gamma ↔
      gamma = canonicalGeneralizedECCoupling n mu nu hMarginals := by
  constructor
  · intro hIntrinsic
    have hCanonicalIntrinsic :=
      (canonicalGeneralizedECCoupling_spec n mu nu hMarginals).1
    exact
      (hCanonicalIntrinsic strictExponentialProfile
        strictExponentialProfile_admissible).2 gamma
          ((hIntrinsic strictExponentialProfile
            strictExponentialProfile_admissible).1)
  · rintro rfl
    exact (canonicalGeneralizedECCoupling_spec n mu nu hMarginals).1

end ConcaveOTLimit

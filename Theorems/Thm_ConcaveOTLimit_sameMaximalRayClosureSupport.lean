import Theorems.Thm_ConcaveOTLimit_sameMaximalRayClosureMeasurable
import Theorems.Thm_ConcaveOTLimit_finiteCouplingAvoidsDiagonalOfMutuallySingular
import Theorems.Thm_ConcaveOTLimit_canonicalRaywiseReplacementAssembly

open Filter MeasureTheory ProbabilityTheory Set

open scoped MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

/-- Mutual singularity removes the only potentially non-Borel part of the
same-ray-closure relation. Thus the assembled replacement is supported on
that relation without assuming its global measurability. -/
theorem assembledRaywiseCoupling_supported_sameMaximalRayClosure_of_mutuallySingular
    {n : Nat}
    {mu nu : FiniteMeasure (Euclidean n)}
    {Gamma : Set (Euclidean n × Euclidean n)}
    (D : MaximalRayKernelDisintegration n mu nu Gamma)
    (gamma : FiniteCoupling mu nu)
    (hSupported : IsSupported gamma Gamma)
    (gammaLift :
      FiniteCoupling
        (maximalRayLiftedSource D)
        (maximalRayLiftedTarget D gamma))
    (hLiftedForward :
      IsSupported gammaLift (liftedRayForwardRelation n))
    (hSingular : FiniteMutuallySingular mu nu) :
    IsSupported
      (assembledRaywiseCoupling D gamma hSupported gammaLift)
      {z | SameMaximalRayClosure Gamma z.1 z.2} := by
  letI : Nonempty (OrientedOpenRay n) := ⟨D.defaultRay⟩
  letI : IsMarkovKernel D.source := D.source_isMarkovKernel
  letI : IsMarkovKernel (D.component gamma) :=
    D.component_isMarkovKernel gamma
  letI : IsMarkovKernel (maximalRayTargetKernel D gamma) :=
    maximalRayTargetKernel_isMarkovKernel D gamma
  letI : IsMarkovKernel (assembledRaywiseKernel D gamma gammaLift) :=
    assembledRaywiseKernel_isMarkovKernel D gamma gammaLift
  let gammaSharp :=
    assembledRaywiseCoupling D gamma hSupported gammaLift
  have hOffDiagonal :
      ∀ᵐ z ∂(gammaSharp.plan :
          Measure (Euclidean n × Euclidean n)),
        z.1 ≠ z.2 :=
    finiteCouplingAvoidsDiagonalOfMutuallySingular
      gammaSharp hSingular
  have hOffDiagonalFiber :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        ∀ᵐ z ∂assembledRaywiseKernel D gamma gammaLift R,
          z.1 ≠ z.2 := by
    apply Measure.ae_ae_of_ae_comp
    rw [assembledRaywiseKernel_reconstruction
      D gamma hSupported gammaLift]
    exact hOffDiagonal
  have hOnRay :=
    assembledRaywiseComponent_on_ray_ae
      D gamma hSupported gammaLift hLiftedForward
  have hSelectedFiber :
      ∀ᵐ R ∂(D.sigma : Measure (OrientedOpenRay n)),
        ∀ᵐ z ∂assembledRaywiseKernel D gamma gammaLift R,
          z ∈ selectedMaximalRayClosureRelation D := by
    filter_upwards
        [D.ray_isMaximal_ae, hOnRay, hOffDiagonalFiber] with
        R hMaximal hR hNe
    filter_upwards [hR, hNe] with z hz hzne
    apply sameMaximalRayClosure_mem_selected_of_ne D hzne
    exact ⟨R, hMaximal, hz⟩
  have hSelected :
      IsSupported gammaSharp
        (selectedMaximalRayClosureRelation D) := by
    change
      ∀ᵐ z ∂(gammaSharp.plan :
          Measure (Euclidean n × Euclidean n)),
        z ∈ selectedMaximalRayClosureRelation D
    rw [← assembledRaywiseKernel_reconstruction
      D gamma hSupported gammaLift]
    exact Measure.ae_comp_of_ae_ae
      (measurableSet_selectedMaximalRayClosureRelation D)
      hSelectedFiber
  exact hSelected.mono
    (selectedMaximalRayClosureRelation_subset_sameMaximalRayClosure D)

end ConcaveOTLimit

import Definitions.Def_ConcaveOTLimitModel
import Theorems.Thm_ConcaveOTLimit_kernelDisintegrationUniqueness

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

section Fiber

variable {X R : Type*}
  [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace R] [StandardBorelSpace R] [Nonempty R]

/-- The AP9.1 conditional measures are almost everywhere carried by their
literal label fibers. This is the `ae` form used by AP9.2 uniqueness. -/
theorem ap91_ae_fiber_eq
    (pointLabel : X -> R) (lambda : Measure X)
    [IsFiniteMeasure lambda] (hpointLabel : Measurable pointLabel) :
    ∀ᵐ r ∂lambda.map pointLabel,
      ∀ᵐ x ∂ap91Disintegration pointLabel lambda r,
        pointLabel x = r := by
  filter_upwards
      [ap91_fiber_pushforward pointLabel lambda hpointLabel] with r hr
  have hmap :
      (ap91Disintegration pointLabel lambda r).map pointLabel =
        Measure.dirac r := by
    simpa [Kernel.map_apply _ hpointLabel, Kernel.id_apply] using hr
  have hdirac : ∀ᵐ s ∂Measure.dirac r, s = r := by
    simp
  rw [← hmap] at hdirac
  exact ae_of_ae_map hpointLabel.aemeasurable hdirac

end Fiber

section GenericProjection

variable {Z X R : Type*}
  [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
  [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace R] [StandardBorelSpace R] [Nonempty R]

omit [StandardBorelSpace Z] [Nonempty Z]
  [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace R] [Nonempty R] in
/-- An a.e. agreement between a label on a measure and a point label after a
projection identifies their pushed-forward bases. -/
theorem labeledDisintegration_commonBase
    (rho : Measure Z) [IsFiniteMeasure rho]
    (lambda : Measure X) [IsFiniteMeasure lambda]
    (projection : Z -> X) (hprojection : Measurable projection)
    (hmarginal : rho.map projection = lambda)
    (pairLabel : Z -> R) (pointLabel : X -> R)
    (hpointLabel : Measurable pointLabel)
    (hlabel :
      pairLabel =ᵐ[rho] pointLabel ∘ projection) :
    rho.map pairLabel = lambda.map pointLabel := by
  calc
    rho.map pairLabel =
        rho.map (pointLabel ∘ projection) :=
      Measure.map_congr hlabel
    _ = (rho.map projection).map pointLabel :=
      (Measure.map_map hpointLabel hprojection).symm
    _ = lambda.map pointLabel := by rw [hmarginal]

omit [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace R] [Nonempty R] in
/-- AP9.1 reconstruction can be rebased from the pair-label distribution to
the common point-label distribution. -/
theorem labeledDisintegration_reconstruction
    (rho : Measure Z) [IsFiniteMeasure rho]
    (lambda : Measure X) [IsFiniteMeasure lambda]
    (projection : Z -> X) (hprojection : Measurable projection)
    (hmarginal : rho.map projection = lambda)
    (pairLabel : Z -> R) (pointLabel : X -> R)
    (hpairLabel : Measurable pairLabel)
    (hpointLabel : Measurable pointLabel)
    (hlabel :
      pairLabel =ᵐ[rho] pointLabel ∘ projection) :
    ap91Disintegration pairLabel rho ∘ₘ lambda.map pointLabel = rho := by
  rw [← labeledDisintegration_commonBase rho lambda projection hprojection
    hmarginal pairLabel pointLabel hpointLabel hlabel]
  exact ap91_reconstruction pairLabel rho hpairLabel

omit [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace R] [Nonempty R] in
/-- Mapping a labeled component kernel through a marginal projection
reconstructs that marginal over the common label base. -/
theorem labeledDisintegration_mapped_reconstruction
    (rho : Measure Z) [IsFiniteMeasure rho]
    (lambda : Measure X) [IsFiniteMeasure lambda]
    (projection : Z -> X) (hprojection : Measurable projection)
    (hmarginal : rho.map projection = lambda)
    (pairLabel : Z -> R) (pointLabel : X -> R)
    (hpairLabel : Measurable pairLabel)
    (hpointLabel : Measurable pointLabel)
    (hlabel :
      pairLabel =ᵐ[rho] pointLabel ∘ projection) :
    (ap91Disintegration pairLabel rho).map projection
        ∘ₘ lambda.map pointLabel =
      lambda := by
  calc
    (ap91Disintegration pairLabel rho).map projection
          ∘ₘ lambda.map pointLabel =
        (ap91Disintegration pairLabel rho
          ∘ₘ lambda.map pointLabel).map projection :=
      (Measure.map_comp _ _ hprojection).symm
    _ = rho.map projection := by
      rw [labeledDisintegration_reconstruction rho lambda projection
        hprojection hmarginal pairLabel pointLabel hpairLabel
        hpointLabel hlabel]
    _ = lambda := hmarginal

/-- If a label on `rho` agrees almost everywhere with a point label after a
measurable projection, then the projected AP9.1 component kernel is the
AP9.1 disintegration of the marginal over their common base. -/
theorem labeledDisintegration_map_ae_eq
    (rho : Measure Z) [IsFiniteMeasure rho]
    (lambda : Measure X) [IsFiniteMeasure lambda]
    (projection : Z -> X) (hprojection : Measurable projection)
    (hmarginal : rho.map projection = lambda)
    (pairLabel : Z -> R) (pointLabel : X -> R)
    (hpairLabel : Measurable pairLabel)
    (hpointLabel : Measurable pointLabel)
    (hlabel :
      pairLabel =ᵐ[rho] pointLabel ∘ projection) :
    (ap91Disintegration pairLabel rho).map projection
      =ᵐ[lambda.map pointLabel]
        ap91Disintegration pointLabel lambda := by
  letI : IsMarkovKernel (ap91Disintegration pairLabel rho) :=
    ap91Disintegration_isMarkovKernel pairLabel rho
  letI : IsMarkovKernel (ap91Disintegration pointLabel lambda) :=
    ap91Disintegration_isMarkovKernel pointLabel lambda
  have hbase :
      rho.map pairLabel = lambda.map pointLabel :=
    labeledDisintegration_commonBase rho lambda projection hprojection
      hmarginal pairLabel pointLabel hpointLabel hlabel
  have hpairFiber :
      ∀ᵐ r ∂rho.map pairLabel,
        ∀ᵐ z ∂ap91Disintegration pairLabel rho r,
          pairLabel z = r :=
    ap91_ae_fiber_eq pairLabel rho hpairLabel
  have hlabelFiber :
      ∀ᵐ r ∂rho.map pairLabel,
        ∀ᵐ z ∂ap91Disintegration pairLabel rho r,
          pairLabel z = pointLabel (projection z) := by
    apply Measure.ae_ae_of_ae_comp
    rw [ap91_reconstruction pairLabel rho hpairLabel]
    simpa [Function.comp_def] using hlabel
  have hmappedFiberPair :
      ∀ᵐ r ∂rho.map pairLabel,
        ∀ᵐ x ∂(ap91Disintegration pairLabel rho).map projection r,
          pointLabel x = r := by
    filter_upwards [hpairFiber, hlabelFiber] with r hr hrl
    rw [Kernel.map_apply _ hprojection]
    apply (ae_map_iff hprojection.aemeasurable
      (measurableSet_eq_fun hpointLabel measurable_const)).2
    filter_upwards [hr, hrl] with z hz hzl
    exact hzl.symm.trans hz
  have hmappedFiber :
      ∀ᵐ r ∂lambda.map pointLabel,
        ∀ᵐ x ∂(ap91Disintegration pairLabel rho).map projection r,
          pointLabel x = r := by
    rw [← hbase]
    exact hmappedFiberPair
  apply ap92_same_base_unique pointLabel hpointLabel
  · exact
      (labeledDisintegration_mapped_reconstruction rho lambda projection
        hprojection hmarginal pairLabel pointLabel hpairLabel hpointLabel
        hlabel).trans
        (ap91_reconstruction pointLabel lambda hpointLabel).symm
  · exact hmappedFiber
  · exact ap91_ae_fiber_eq pointLabel lambda hpointLabel

end GenericProjection

section Coupling

variable {X Y R : Type*}
  [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableSpace R] [StandardBorelSpace R] [Nonempty R]

/-- The conditional component kernel of a finite coupling, indexed by a
label on source-target pairs. -/
noncomputable def labeledCouplingComponent
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (pairLabel : X × Y -> R) (gamma : FiniteCoupling mu nu) :
    Kernel R (X × Y) :=
  ap91Disintegration pairLabel (gamma.plan : Measure (X × Y))

omit [StandardBorelSpace R] [Nonempty R] in
/-- Every labeled coupling component is a Markov kernel. -/
theorem labeledCouplingComponent_isMarkovKernel
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (pairLabel : X × Y -> R) (gamma : FiniteCoupling mu nu) :
    IsMarkovKernel (labeledCouplingComponent pairLabel gamma) :=
  ap91Disintegration_isMarkovKernel pairLabel
    (gamma.plan : Measure (X × Y))

omit [StandardBorelSpace R] [Nonempty R] in
/-- The component kernel reconstructs the coupling over its own pair-label
distribution. -/
theorem labeledCouplingComponent_reconstruction
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu) (pairLabel : X × Y -> R)
    (hpairLabel : Measurable pairLabel) :
    labeledCouplingComponent pairLabel gamma
        ∘ₘ Measure.map pairLabel
          (gamma.plan : Measure (X × Y)) =
      (gamma.plan : Measure (X × Y)) := by
  exact ap91_reconstruction pairLabel
    (gamma.plan : Measure (X × Y)) hpairLabel

omit [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
  [StandardBorelSpace R] [Nonempty R] in
/-- A source point label agreeing with the pair label gives the same finite
pushed-forward base. -/
theorem labeledCoupling_source_commonBase
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    (pairLabel : X × Y -> R) (sourceLabel : X -> R)
    (hsourceLabel : Measurable sourceLabel)
    (hlabel :
      pairLabel =ᵐ[(gamma.plan : Measure (X × Y))]
        sourceLabel ∘ (Prod.fst : X × Y -> X)) :
    gamma.plan.map pairLabel = mu.map sourceLabel := by
  have hmarginal :
      Measure.map (Prod.fst : X × Y -> X)
          (gamma.plan : Measure (X × Y)) =
        (mu : Measure X) := by
    simpa [firstMarginal, FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure X => (eta : Measure X))
      gamma.property.1
  apply FiniteMeasure.toMeasure_injective
  exact labeledDisintegration_commonBase
    (gamma.plan : Measure (X × Y)) (mu : Measure X)
    (Prod.fst : X × Y -> X) measurable_fst hmarginal
    pairLabel sourceLabel hsourceLabel hlabel

omit [StandardBorelSpace X] [Nonempty X]
  [StandardBorelSpace Y] [Nonempty Y]
  [StandardBorelSpace R] [Nonempty R] in
/-- A target point label agreeing with the pair label gives the same finite
pushed-forward base. -/
theorem labeledCoupling_target_commonBase
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    (pairLabel : X × Y -> R) (targetLabel : Y -> R)
    (htargetLabel : Measurable targetLabel)
    (hlabel :
      pairLabel =ᵐ[(gamma.plan : Measure (X × Y))]
        targetLabel ∘ (Prod.snd : X × Y -> Y)) :
    gamma.plan.map pairLabel = nu.map targetLabel := by
  have hmarginal :
      Measure.map (Prod.snd : X × Y -> Y)
          (gamma.plan : Measure (X × Y)) =
        (nu : Measure Y) := by
    simpa [secondMarginal, FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure Y => (eta : Measure Y))
      gamma.property.2
  apply FiniteMeasure.toMeasure_injective
  exact labeledDisintegration_commonBase
    (gamma.plan : Measure (X × Y)) (nu : Measure Y)
    (Prod.snd : X × Y -> Y) measurable_snd hmarginal
    pairLabel targetLabel htargetLabel hlabel

omit [StandardBorelSpace R] [Nonempty R] in
/-- The coupling component reconstructs the plan over the common source
point-label base. -/
theorem labeledCouplingComponent_reconstruction_source
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    (pairLabel : X × Y -> R) (sourceLabel : X -> R)
    (hpairLabel : Measurable pairLabel)
    (hsourceLabel : Measurable sourceLabel)
    (hlabel :
      pairLabel =ᵐ[(gamma.plan : Measure (X × Y))]
        sourceLabel ∘ (Prod.fst : X × Y -> X)) :
    labeledCouplingComponent pairLabel gamma
        ∘ₘ Measure.map sourceLabel (mu : Measure X) =
      (gamma.plan : Measure (X × Y)) := by
  have hmarginal :
      Measure.map (Prod.fst : X × Y -> X)
          (gamma.plan : Measure (X × Y)) =
        (mu : Measure X) := by
    simpa [firstMarginal, FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure X => (eta : Measure X))
      gamma.property.1
  exact labeledDisintegration_reconstruction
    (gamma.plan : Measure (X × Y)) (mu : Measure X)
    (Prod.fst : X × Y -> X) measurable_fst hmarginal
    pairLabel sourceLabel hpairLabel hsourceLabel hlabel

omit [StandardBorelSpace R] [Nonempty R] in
/-- The coupling component reconstructs the plan over the common target
point-label base. -/
theorem labeledCouplingComponent_reconstruction_target
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    (pairLabel : X × Y -> R) (targetLabel : Y -> R)
    (hpairLabel : Measurable pairLabel)
    (htargetLabel : Measurable targetLabel)
    (hlabel :
      pairLabel =ᵐ[(gamma.plan : Measure (X × Y))]
        targetLabel ∘ (Prod.snd : X × Y -> Y)) :
    labeledCouplingComponent pairLabel gamma
        ∘ₘ Measure.map targetLabel (nu : Measure Y) =
      (gamma.plan : Measure (X × Y)) := by
  have hmarginal :
      Measure.map (Prod.snd : X × Y -> Y)
          (gamma.plan : Measure (X × Y)) =
        (nu : Measure Y) := by
    simpa [secondMarginal, FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure Y => (eta : Measure Y))
      gamma.property.2
  exact labeledDisintegration_reconstruction
    (gamma.plan : Measure (X × Y)) (nu : Measure Y)
    (Prod.snd : X × Y -> Y) measurable_snd hmarginal
    pairLabel targetLabel hpairLabel htargetLabel hlabel

omit [StandardBorelSpace R] [Nonempty R] in
/-- The source marginal of the coupling component reconstructs `mu` over
the common source-label base. -/
theorem labeledCouplingComponent_source_reconstruction
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    (pairLabel : X × Y -> R) (sourceLabel : X -> R)
    (hpairLabel : Measurable pairLabel)
    (hsourceLabel : Measurable sourceLabel)
    (hlabel :
      pairLabel =ᵐ[(gamma.plan : Measure (X × Y))]
        sourceLabel ∘ (Prod.fst : X × Y -> X)) :
    (labeledCouplingComponent pairLabel gamma).map Prod.fst
        ∘ₘ Measure.map sourceLabel (mu : Measure X) =
      (mu : Measure X) := by
  have hmarginal :
      Measure.map (Prod.fst : X × Y -> X)
          (gamma.plan : Measure (X × Y)) =
        (mu : Measure X) := by
    simpa [firstMarginal, FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure X => (eta : Measure X))
      gamma.property.1
  exact labeledDisintegration_mapped_reconstruction
    (gamma.plan : Measure (X × Y)) (mu : Measure X)
    (Prod.fst : X × Y -> X) measurable_fst hmarginal
    pairLabel sourceLabel hpairLabel hsourceLabel hlabel

omit [StandardBorelSpace R] [Nonempty R] in
/-- The target marginal of the coupling component reconstructs `nu` over
the common target-label base. -/
theorem labeledCouplingComponent_target_reconstruction
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    (pairLabel : X × Y -> R) (targetLabel : Y -> R)
    (hpairLabel : Measurable pairLabel)
    (htargetLabel : Measurable targetLabel)
    (hlabel :
      pairLabel =ᵐ[(gamma.plan : Measure (X × Y))]
        targetLabel ∘ (Prod.snd : X × Y -> Y)) :
    (labeledCouplingComponent pairLabel gamma).map Prod.snd
        ∘ₘ Measure.map targetLabel (nu : Measure Y) =
      (nu : Measure Y) := by
  have hmarginal :
      Measure.map (Prod.snd : X × Y -> Y)
          (gamma.plan : Measure (X × Y)) =
        (nu : Measure Y) := by
    simpa [secondMarginal, FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure Y => (eta : Measure Y))
      gamma.property.2
  exact labeledDisintegration_mapped_reconstruction
    (gamma.plan : Measure (X × Y)) (nu : Measure Y)
    (Prod.snd : X × Y -> Y) measurable_snd hmarginal
    pairLabel targetLabel hpairLabel htargetLabel hlabel

/-- Source bridge: the first marginal kernel of the pair-labeled
conditional components is the point-measure conditional kernel. -/
theorem labeledCouplingComponent_map_fst_ae_eq
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    (pairLabel : X × Y -> R) (sourceLabel : X -> R)
    (hpairLabel : Measurable pairLabel)
    (hsourceLabel : Measurable sourceLabel)
    (hlabel :
      pairLabel =ᵐ[(gamma.plan : Measure (X × Y))]
        sourceLabel ∘ (Prod.fst : X × Y -> X)) :
    (labeledCouplingComponent pairLabel gamma).map Prod.fst
      =ᵐ[Measure.map sourceLabel (mu : Measure X)]
        ap91Disintegration sourceLabel (mu : Measure X) := by
  have hmarginal :
      Measure.map (Prod.fst : X × Y -> X)
          (gamma.plan : Measure (X × Y)) =
        (mu : Measure X) := by
    simpa [firstMarginal, FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure X => (eta : Measure X))
      gamma.property.1
  exact labeledDisintegration_map_ae_eq
    (gamma.plan : Measure (X × Y)) (mu : Measure X)
    (Prod.fst : X × Y -> X) measurable_fst hmarginal
    pairLabel sourceLabel hpairLabel hsourceLabel hlabel

/-- Target bridge: the second marginal kernel of the pair-labeled
conditional components is the point-measure conditional kernel. -/
theorem labeledCouplingComponent_map_snd_ae_eq
    {mu : FiniteMeasure X} {nu : FiniteMeasure Y}
    (gamma : FiniteCoupling mu nu)
    (pairLabel : X × Y -> R) (targetLabel : Y -> R)
    (hpairLabel : Measurable pairLabel)
    (htargetLabel : Measurable targetLabel)
    (hlabel :
      pairLabel =ᵐ[(gamma.plan : Measure (X × Y))]
        targetLabel ∘ (Prod.snd : X × Y -> Y)) :
    (labeledCouplingComponent pairLabel gamma).map Prod.snd
      =ᵐ[Measure.map targetLabel (nu : Measure Y)]
        ap91Disintegration targetLabel (nu : Measure Y) := by
  have hmarginal :
      Measure.map (Prod.snd : X × Y -> Y)
          (gamma.plan : Measure (X × Y)) =
        (nu : Measure Y) := by
    simpa [secondMarginal, FiniteCoupling.plan] using congrArg
      (fun eta : FiniteMeasure Y => (eta : Measure Y))
      gamma.property.2
  exact labeledDisintegration_map_ae_eq
    (gamma.plan : Measure (X × Y)) (nu : Measure Y)
    (Prod.snd : X × Y -> Y) measurable_snd hmarginal
    pairLabel targetLabel hpairLabel htargetLabel hlabel

end Coupling

end ConcaveOTLimit

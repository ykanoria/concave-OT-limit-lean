import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Probability.Kernel.CondDistrib

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

variable {X Y : Type*}

section Disintegration

variable [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace Y]

/-- The conditional-distribution model of disintegration along a measurable
label map. -/
noncomputable def ap91Disintegration
    (pi : X -> Y) (lambda : Measure X) [IsFiniteMeasure lambda] :
    Kernel Y X :=
  condDistrib id pi lambda

/-- The selected conditional measures are probability measures at every
label. -/
theorem ap91Disintegration_isMarkovKernel
    (pi : X -> Y) (lambda : Measure X) [IsFiniteMeasure lambda] :
    IsMarkovKernel (ap91Disintegration pi lambda) := by
  unfold ap91Disintegration
  infer_instance

/-- Reconstruction of a finite measure from its label distribution and
conditional measures. -/
theorem ap91_reconstruction
    (pi : X -> Y) (lambda : Measure X) [IsFiniteMeasure lambda]
    (hpi : Measurable pi) :
    ap91Disintegration pi lambda ∘ₘ lambda.map pi = lambda := by
  rw [ap91Disintegration,
    condDistrib_comp_map hpi.aemeasurable measurable_id.aemeasurable,
    Measure.map_id]

/-- Joint reconstruction after retaining both the label and the original
point. -/
theorem ap91_joint_reconstruction
    (pi : X -> Y) (lambda : Measure X) [IsFiniteMeasure lambda] :
    lambda.map pi ⊗ₘ ap91Disintegration pi lambda =
      lambda.map (fun x => (pi x, x)) := by
  exact compProd_map_condDistrib measurable_id.aemeasurable

variable [StandardBorelSpace Y] [Nonempty Y]

/-- A conditional measure pushed forward by its label map is the Dirac mass
at that label, almost everywhere. -/
theorem ap91_fiber_pushforward
    (pi : X -> Y) (lambda : Measure X) [IsFiniteMeasure lambda]
    (hpi : Measurable pi) :
    (ap91Disintegration pi lambda).map pi
      =ᵐ[lambda.map pi] Kernel.id := by
  have hcomp :
      condDistrib (pi ∘ id) pi lambda =ᵐ[lambda.map pi]
        (condDistrib (id : X -> X) pi lambda).map pi :=
    condDistrib_comp (mβ := (inferInstance : MeasurableSpace Y))
      (mΩ' := (inferInstance : MeasurableSpace Y))
      (μ := lambda) (Y := (id : X -> X)) pi
      measurable_id.aemeasurable hpi
  have hself := condDistrib_self (μ := lambda) pi
  simpa [ap91Disintegration, Function.comp_def] using
    hcomp.symm.trans hself

/-- Almost every conditional measure gives mass one to its literal label
fiber. -/
theorem ap91_fiber_concentration
    (pi : X -> Y) (lambda : Measure X) [IsFiniteMeasure lambda]
    (hpi : Measurable pi) :
    ∀ᵐ y ∂lambda.map pi,
      ap91Disintegration pi lambda y (pi ⁻¹' {y}) = 1 := by
  filter_upwards [ap91_fiber_pushforward pi lambda hpi] with y hy
  have hyMeasure :
      (ap91Disintegration pi lambda y).map pi = Measure.dirac y := by
    simpa [Kernel.map_apply _ hpi, Kernel.id_apply] using hy
  have hy' := congrArg (fun nu : Measure Y => nu {y}) hyMeasure
  change
    (ap91Disintegration pi lambda y).map pi {y} =
      Measure.dirac y {y} at hy'
  rw [Measure.map_apply hpi (measurableSet_singleton y),
    Measure.dirac_apply' _ (measurableSet_singleton y)] at hy'
  simpa using hy'

end Disintegration

section FiniteFibers

variable (R X : Type*) [MeasurableSpace R] [MeasurableSpace X]

/-- A kernel together with bundled finite versions of all its fibers. -/
structure FiniteKernelFamily where
  toKernel : Kernel R X
  fiber : R -> FiniteMeasure X
  coe_fiber : forall r, (fiber r : Measure X) = toKernel r

namespace FiniteKernelFamily

/-- Bundle every fiber of a Markov kernel as a finite measure. -/
noncomputable def ofMarkovKernel
    (kappa : Kernel R X) [IsMarkovKernel kappa] :
    FiniteKernelFamily R X where
  toKernel := kappa
  fiber := fun r => ⟨kappa r, inferInstance⟩
  coe_fiber := fun _ => rfl

@[simp]
theorem ofMarkovKernel_toKernel
    (kappa : Kernel R X) [IsMarkovKernel kappa] :
    (ofMarkovKernel R X kappa).toKernel = kappa :=
  rfl

@[simp]
theorem ofMarkovKernel_coe_fiber
    (kappa : Kernel R X) [IsMarkovKernel kappa] (r : R) :
    ((ofMarkovKernel R X kappa).fiber r : Measure X) = kappa r :=
  rfl

end FiniteKernelFamily

end FiniteFibers

/-- Setwise form of a kernel reconstruction identity. -/
theorem kernel_reconstruction_setwise
    {R X : Type*}
    [MeasurableSpace R] [MeasurableSpace X]
    (sigma : FiniteMeasure R)
    (kappa : Kernel R X) [IsFiniteKernel kappa]
    (lambda : FiniteMeasure X)
    (hreconstruct :
      kappa ∘ₘ (sigma : Measure R) = (lambda : Measure X)) :
    forall s : Set X, MeasurableSet s ->
      (lambda : Measure X) s =
        ∫⁻ r, kappa r s ∂(sigma : Measure R) := by
  intro s hs
  rw [← hreconstruct, Measure.bind_apply hs kappa.aemeasurable]

end ConcaveOTLimit

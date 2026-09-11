import Theorems.Thm_ConcaveOTLimit_kernelDisintegration
import Mathlib.Probability.Kernel.CompProdEqIff

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal MeasureTheory ProbabilityTheory

noncomputable section

namespace ConcaveOTLimit

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A composition-product is carried by the graph of its fiber label when
almost every kernel fiber is carried by the corresponding level set. -/
theorem ae_compProd_fiber_of_ae_fiber
    [MeasurableEq Y]
    {mu : Measure Y} {kappa : Kernel Y X}
    [IsFiniteMeasure mu] [IsFiniteKernel kappa]
    (pi : X -> Y) (hpi : Measurable pi)
    (hfiber : ∀ᵐ y ∂mu, ∀ᵐ x ∂kappa y, pi x = y) :
    ∀ᵐ p ∂mu ⊗ₘ kappa, p.1 = pi p.2 := by
  apply Measure.ae_compProd_of_ae_ae
  · exact measurableSet_eq_fun measurable_fst (hpi.comp measurable_snd)
  · filter_upwards [hfiber] with y hy
    filter_upwards [hy] with x hx using hx.symm

/-- A composition-product carried by a label graph is the graph-map of its
second marginal. -/
theorem compProd_eq_graphMap_comp
    {mu : Measure Y} {kappa : Kernel Y X}
    [IsFiniteMeasure mu] [IsFiniteKernel kappa]
    (pi : X -> Y) (hpi : Measurable pi)
    (hfiber : ∀ᵐ p ∂mu ⊗ₘ kappa, p.1 = pi p.2) :
    mu ⊗ₘ kappa =
      (kappa ∘ₘ mu).map (fun x => (pi x, x)) := by
  let graph : X -> Y × X := fun x => (pi x, x)
  have hgraph : Measurable graph := hpi.prodMk measurable_id
  have hae :
      (fun p : Y × X => p) =ᵐ[mu ⊗ₘ kappa]
        fun p => graph p.2 := by
    filter_upwards [hfiber] with p hp
    exact Prod.ext hp rfl
  calc
    mu ⊗ₘ kappa = (mu ⊗ₘ kappa).map id := (Measure.map_id).symm
    _ = (mu ⊗ₘ kappa).map (fun p => graph p.2) :=
      Measure.map_congr hae
    _ = ((mu ⊗ₘ kappa).map Prod.snd).map graph := by
      rw [Measure.map_map hgraph measurable_snd]
      rfl
    _ = (kappa ∘ₘ mu).map graph := by
      rw [← Measure.snd, Measure.snd_compProd]

/-- Finite kernels over the same base are almost everywhere equal when they
reconstruct the same measure and are carried by the same label fibers. -/
theorem ap92_same_base_unique
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y]
    {mu : Measure Y} {kappa eta : Kernel Y X}
    [IsFiniteMeasure mu] [IsFiniteKernel kappa] [IsFiniteKernel eta]
    (pi : X -> Y) (hpi : Measurable pi)
    (hreconstruct : kappa ∘ₘ mu = eta ∘ₘ mu)
    (hkappaFiber : ∀ᵐ y ∂mu, ∀ᵐ x ∂kappa y, pi x = y)
    (hetaFiber : ∀ᵐ y ∂mu, ∀ᵐ x ∂eta y, pi x = y) :
    kappa =ᵐ[mu] eta := by
  apply Kernel.ae_eq_of_compProd_eq
  rw [compProd_eq_graphMap_comp pi hpi
      (ae_compProd_fiber_of_ae_fiber pi hpi hkappaFiber),
    compProd_eq_graphMap_comp pi hpi
      (ae_compProd_fiber_of_ae_fiber pi hpi hetaFiber),
    hreconstruct]

end ConcaveOTLimit

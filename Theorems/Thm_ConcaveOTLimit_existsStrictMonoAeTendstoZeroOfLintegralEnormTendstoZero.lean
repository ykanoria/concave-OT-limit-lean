import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open Filter MeasureTheory Topology
open scoped ENNReal

namespace ConcaveOTLimit

/-- If the `L¹` seminorms of a sequence of a.e. strongly measurable real
functions tend to zero, then a subsequence tends to zero almost everywhere. -/
theorem existsStrictMonoAeTendstoZeroOfLintegralEnormTendstoZero
    {Omega : Type*} [MeasurableSpace Omega]
    (plan : Measure Omega) (f : Nat -> Omega -> Real)
    (hf : forall n, AEStronglyMeasurable (f n) plan)
    (hTendsto :
      Tendsto (fun n => ∫⁻ x, ‖f n x‖ₑ ∂plan) atTop (nhds 0)) :
    ∃ k : Nat -> Nat, StrictMono k ∧
      ∀ᵐ x ∂plan, Tendsto (fun n => f (k n) x) atTop (nhds 0) := by
  have hLpNorm :
      Tendsto
        (fun n => eLpNorm (f n - (0 : Omega -> Real)) 1 plan)
        atTop (nhds 0) := by
    simpa [eLpNorm_one_eq_lintegral_enorm] using hTendsto
  have hInMeasure : TendstoInMeasure plan f atTop (0 : Omega -> Real) :=
    tendstoInMeasure_of_tendsto_eLpNorm
      (p := (1 : ENNReal)) one_ne_zero hf aestronglyMeasurable_zero hLpNorm
  simpa using hInMeasure.exists_seq_tendsto_ae

end ConcaveOTLimit

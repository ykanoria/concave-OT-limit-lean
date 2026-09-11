import Mathlib.MeasureTheory.Measure.Support
import Theorems.Thm_ConcaveOTLimit_finiteCouplingAvoidsDiagonalOfMutuallySingular

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    {mu nu : FiniteMeasure Real}
    {gamma : FiniteCoupling mu nu}
    (hSingular : FiniteMutuallySingular mu nu)
    (hForward : IsForwardPlan gamma) :
    exists S : Set (Real × Real),
      MeasurableSet S /\
      IsSupported gamma S /\
      (forall {x y : Real}, (x, y) ∈ S -> x < y) /\
      S ⊆ Measure.support
        (gamma.plan : Measure (Real × Real)) := by
  have hOffDiagonal :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.1 ≠ z.2 :=
    finiteCouplingAvoidsDiagonalOfMutuallySingular gamma hSingular
  have hStrict :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.1 < z.2 := by
    filter_upwards [hForward, hOffDiagonal] with z hzForward hzNe
    exact lt_of_le_of_ne hzForward hzNe
  have hTopologicalSupport :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)),
        z ∈ Measure.support
          (gamma.plan : Measure (Real × Real)) :=
    Measure.support_mem_ae
  let S : Set (Real × Real) :=
    Measure.support (gamma.plan : Measure (Real × Real)) ∩
      {z : Real × Real | z.1 < z.2}
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · exact Measure.isClosed_support.measurableSet.inter
      (measurableSet_lt measurable_fst measurable_snd)
  · filter_upwards [hTopologicalSupport, hStrict] with z hzSupport hzStrict
    exact ⟨hzSupport, hzStrict⟩
  · intro x y hxy
    exact hxy.2
  · intro z hz
    exact hz.1

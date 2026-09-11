import Theorems.Thm_ConcaveOTLimit_finiteCouplingAvoidsDiagonalOfMutuallySingular
import Theorems.Thm_ConcaveOTLimit_isForwardPlanOfJuilletExcursionPlan

open MeasureTheory Set

namespace ConcaveOTLimit

/-- A Juillet excursion coupling of mutually singular marginals has a
measurable full-mass monotone-arch support consisting of strictly forward
pairs. -/
theorem existsStrictMonotoneArchSupportOfJuilletExcursionPlan
    {mu nu : FiniteMeasure Real}
    {gamma : FiniteCoupling mu nu}
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (hExcursion : IsJuilletExcursionPlan mu nu gamma.plan) :
    exists S : Set (Real × Real),
      MeasurableSet S /\
      IsSupported gamma S /\
      (forall {x y : Real}, (x, y) ∈ S -> x < y) /\
      IsMonotoneArchSet S := by
  have hForward : IsForwardPlan gamma :=
    isForwardPlanOfJuilletExcursionPlan hAtomless hOrder hExcursion
  have hOffDiagonal :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.1 ≠ z.2 :=
    finiteCouplingAvoidsDiagonalOfMutuallySingular gamma hSingular
  have hStrict :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.1 < z.2 := by
    filter_upwards [hForward, hOffDiagonal] with z hzForward hzNe
    exact lt_of_le_of_ne hzForward hzNe
  rcases hExcursion with
    ⟨_hCoupling, support, hMeasurable, hFull, hMonotone⟩
  let S : Set (Real × Real) :=
    support ∩ {z : Real × Real | z.1 < z.2}
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · exact hMeasurable.inter
      (measurableSet_lt measurable_fst measurable_snd)
  · filter_upwards [hFull, hStrict] with z hzSupport hzStrict
    exact ⟨hzSupport, hzStrict⟩
  · intro x y hxy
    exact hxy.2
  · intro p hp q hq
    exact hMonotone p hp.1 q hq.1

end ConcaveOTLimit

import Theorems.Thm_ConcaveOTLimit_oppositeMonotoneArchesCannotCrossCut
import Mathlib.MeasureTheory.Measure.Restrict

open MeasureTheory Set

open ConcaveOTLimit

private theorem measurePreservingFst
    {mu nu : FiniteMeasure Real} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.fst
      (gamma.plan : Measure (Real × Real)) (mu : Measure Real) := by
  refine ⟨measurable_fst, ?_⟩
  simpa [firstMarginal] using congrArg
    (fun eta : FiniteMeasure Real => (eta : Measure Real)) gamma.property.1

private theorem measurePreservingSnd
    {mu nu : FiniteMeasure Real} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.snd
      (gamma.plan : Measure (Real × Real)) (nu : Measure Real) := by
  refine ⟨measurable_snd, ?_⟩
  simpa [secondMarginal] using congrArg
    (fun eta : FiniteMeasure Real => (eta : Measure Real)) gamma.property.2

theorem solution
    {mu nu : FiniteMeasure Real}
    {gamma : FiniteCoupling mu nu}
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (hExcursion : IsJuilletExcursionPlan mu nu gamma.plan) :
    IsForwardPlan gamma := by
  rcases hExcursion with
    ⟨_hCoupling, support, _hSupportMeasurable, hFull, hMonotone⟩
  by_contra hNotForward
  change ¬(∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.1 <= z.2)
    at hNotForward
  let backward : Set (Real × Real) := {z | z.2 < z.1}
  let backwardAt : Rat -> Set (Real × Real) :=
    fun q => {z | z.2 <= (q : Real) /\ (q : Real) < z.1}
  have hBackwardSubset :
      backward ⊆ ⋃ q : Rat, backwardAt q := by
    intro z hz
    change z.2 < z.1 at hz
    obtain ⟨q, hzq, hqz⟩ := exists_rat_btwn hz
    apply mem_iUnion.mpr
    exact ⟨q, hzq.le, hqz⟩
  have hBackwardMeasureNe :
      (gamma.plan : Measure (Real × Real)) backward ≠ 0 := by
    intro hZero
    apply hNotForward
    apply ae_iff.mpr
    simpa only [backward, not_le, setOf_mem_eq] using hZero
  have hUnionMeasureNe :
      (gamma.plan : Measure (Real × Real))
          (⋃ q : Rat, backwardAt q) ≠ 0 := by
    intro hZero
    exact hBackwardMeasureNe
      (measure_mono_null hBackwardSubset hZero)
  obtain ⟨q, hBackwardAtPos⟩ :=
    exists_measure_pos_of_not_measure_iUnion_null hUnionMeasureNe
  let cut : Real := q
  let sourceLeft : Set (Real × Real) := {z | z.1 <= cut}
  let targetLeft : Set (Real × Real) := {z | z.2 <= cut}
  let forwardAt : Set (Real × Real) :=
    {z | z.1 <= cut /\ cut < z.2}
  have hSourceLeftMeasurable : MeasurableSet sourceLeft :=
    measurableSet_le measurable_fst measurable_const
  have hTargetLeftMeasurable : MeasurableSet targetLeft :=
    measurableSet_le measurable_snd measurable_const
  have hForwardDiff : sourceLeft \ targetLeft = forwardAt := by
    ext z
    simp only [sourceLeft, targetLeft, forwardAt, mem_diff, mem_setOf_eq,
      not_le]
  have hBackwardDiff : targetLeft \ sourceLeft = backwardAt q := by
    ext z
    simp only [targetLeft, sourceLeft, backwardAt, cut, mem_diff,
      mem_setOf_eq, not_le]
  have hSourceMeasure :
      (gamma.plan : Measure (Real × Real)) sourceLeft =
        (mu : Measure Real) (Iic cut) := by
    calc
      (gamma.plan : Measure (Real × Real)) sourceLeft =
          Measure.map Prod.fst
            (gamma.plan : Measure (Real × Real)) (Iic cut) := by
        rw [Measure.map_apply measurable_fst measurableSet_Iic]
        rfl
      _ = (mu : Measure Real) (Iic cut) := by
        rw [(measurePreservingFst gamma).map_eq]
  have hTargetMeasure :
      (gamma.plan : Measure (Real × Real)) targetLeft =
        (nu : Measure Real) (Iic cut) := by
    calc
      (gamma.plan : Measure (Real × Real)) targetLeft =
          Measure.map Prod.snd
            (gamma.plan : Measure (Real × Real)) (Iic cut) := by
        rw [Measure.map_apply measurable_snd measurableSet_Iic]
        rfl
      _ = (nu : Measure Real) (Iic cut) := by
        rw [(measurePreservingSnd gamma).map_eq]
  have hPlanOrder :
      (gamma.plan : Measure (Real × Real)) targetLeft <=
        (gamma.plan : Measure (Real × Real)) sourceLeft := by
    rw [hTargetMeasure, hSourceMeasure]
    exact hOrder cut
  have hSourceDecomp :
      (gamma.plan : Measure (Real × Real)) forwardAt +
          (gamma.plan : Measure (Real × Real))
            (sourceLeft ∩ targetLeft) =
        (gamma.plan : Measure (Real × Real)) sourceLeft := by
    rw [← hForwardDiff]
    exact measure_diff_add_inter sourceLeft hTargetLeftMeasurable
  have hTargetDecomp :
      (gamma.plan : Measure (Real × Real)) (backwardAt q) +
          (gamma.plan : Measure (Real × Real))
            (sourceLeft ∩ targetLeft) =
        (gamma.plan : Measure (Real × Real)) targetLeft := by
    rw [← hBackwardDiff]
    simpa only [inter_comm] using
      (measure_diff_add_inter
        (μ := (gamma.plan : Measure (Real × Real)))
        targetLeft hSourceLeftMeasurable)
  have hBackwardLeForward :
      (gamma.plan : Measure (Real × Real)) (backwardAt q) <=
        (gamma.plan : Measure (Real × Real)) forwardAt := by
    apply ENNReal.le_of_add_le_add_left
      (measure_ne_top
        (gamma.plan : Measure (Real × Real))
        (sourceLeft ∩ targetLeft))
    calc
      (gamma.plan : Measure (Real × Real)) (sourceLeft ∩ targetLeft) +
          (gamma.plan : Measure (Real × Real)) (backwardAt q) =
        (gamma.plan : Measure (Real × Real)) targetLeft := by
          rw [add_comm, hTargetDecomp]
      _ <= (gamma.plan : Measure (Real × Real)) sourceLeft := hPlanOrder
      _ = (gamma.plan : Measure (Real × Real)) (sourceLeft ∩ targetLeft) +
          (gamma.plan : Measure (Real × Real)) forwardAt := by
          rw [← hSourceDecomp, add_comm]
  have hForwardAtPos :
      0 < (gamma.plan : Measure (Real × Real)) forwardAt :=
    hBackwardAtPos.trans_le hBackwardLeForward
  let sourceAt : Set (Real × Real) := {z | z.1 = cut}
  have hSourceAtZero :
      (gamma.plan : Measure (Real × Real)) sourceAt = 0 := by
    calc
      (gamma.plan : Measure (Real × Real)) sourceAt =
          Measure.map Prod.fst
            (gamma.plan : Measure (Real × Real)) {cut} := by
        rw [Measure.map_apply measurable_fst (measurableSet_singleton cut)]
        rfl
      _ = (mu : Measure Real) {cut} := by
        rw [(measurePreservingFst gamma).map_eq]
      _ = 0 := hAtomless cut
  have hStrictForwardAtPos :
      0 <
        (gamma.plan : Measure (Real × Real)) (forwardAt \ sourceAt) := by
    rw [measure_diff_null hSourceAtZero]
    exact hForwardAtPos
  obtain ⟨backwardPoint, hBackwardPoint, hBackwardSupport⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae
      hBackwardAtPos.ne'
      (ae_restrict_of_ae hFull)
  obtain ⟨forwardPoint, hForwardPoint, hForwardSupport⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae
      hStrictForwardAtPos.ne'
      (ae_restrict_of_ae hFull)
  have hForwardSourceNe : forwardPoint.1 ≠ cut := by
    simpa only [sourceAt, mem_setOf_eq] using hForwardPoint.2
  have hForwardStrict : forwardPoint.1 < cut :=
    lt_of_le_of_ne hForwardPoint.1.1 hForwardSourceNe
  have hConditions :=
    hMonotone backwardPoint hBackwardSupport forwardPoint hForwardSupport
  have hConditionsRev :=
    hMonotone forwardPoint hForwardSupport backwardPoint hBackwardSupport
  exact oppositeMonotoneArchesCannotCrossCut
    ⟨hBackwardPoint.1, hBackwardPoint.2⟩
    ⟨hForwardStrict, hForwardPoint.1.2⟩
    hConditions.1 hConditions.2.1 hConditionsRev.2.1
    hConditions.2.2 hConditionsRev.2.2

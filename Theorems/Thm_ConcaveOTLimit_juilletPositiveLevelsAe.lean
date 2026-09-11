import Theorems.Thm_ConcaveOTLimit_existsStrictMonotoneArchSupportOfJuilletExcursionPlan
import Definitions.Def_JuilletCanonicalRoutes
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory Set

namespace ConcaveOTLimit

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

private theorem signedCumulative_eq_forwardCrossing
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (hForward : IsForwardPlan gamma) (c : Real) :
    signedCumulative mu nu c =
      ((gamma.plan : Measure (Real × Real))
        {z | z.1 <= c ∧ c < z.2}).toReal := by
  let sourceLeft : Set (Real × Real) := {z | z.1 <= c}
  let targetLeft : Set (Real × Real) := {z | z.2 <= c}
  let crossing : Set (Real × Real) := {z | z.1 <= c ∧ c < z.2}
  have hTargetMeasurable : MeasurableSet targetLeft :=
    measurableSet_le measurable_snd measurable_const
  have hSourceDiff : sourceLeft \ targetLeft = crossing := by
    ext z
    simp only [sourceLeft, targetLeft, crossing, mem_diff, mem_setOf_eq,
      not_le]
  have hSourceMeasure :
      (gamma.plan : Measure (Real × Real)) sourceLeft =
        (mu : Measure Real) (Iic c) := by
    calc
      (gamma.plan : Measure (Real × Real)) sourceLeft =
          Measure.map Prod.fst
            (gamma.plan : Measure (Real × Real)) (Iic c) := by
        rw [Measure.map_apply measurable_fst measurableSet_Iic]
        rfl
      _ = (mu : Measure Real) (Iic c) := by
        rw [(measurePreservingFst gamma).map_eq]
  have hTargetMeasure :
      (gamma.plan : Measure (Real × Real)) targetLeft =
        (nu : Measure Real) (Iic c) := by
    calc
      (gamma.plan : Measure (Real × Real)) targetLeft =
          Measure.map Prod.snd
            (gamma.plan : Measure (Real × Real)) (Iic c) := by
        rw [Measure.map_apply measurable_snd measurableSet_Iic]
        rfl
      _ = (nu : Measure Real) (Iic c) := by
        rw [(measurePreservingSnd gamma).map_eq]
  have hTargetInter :
      (gamma.plan : Measure (Real × Real))
          (sourceLeft ∩ targetLeft) =
        (gamma.plan : Measure (Real × Real)) targetLeft := by
    apply measure_congr
    filter_upwards [hForward] with z hz
    change (z.1 <= c ∧ z.2 <= c) = (z.2 <= c)
    apply propext
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨hz.trans h, h⟩
  have hDecomp :
      (gamma.plan : Measure (Real × Real)) crossing +
          (gamma.plan : Measure (Real × Real)) targetLeft =
        (gamma.plan : Measure (Real × Real)) sourceLeft := by
    rw [← hTargetInter, ← hSourceDiff]
    exact measure_diff_add_inter sourceLeft hTargetMeasurable
  rw [signedCumulative, ← hSourceMeasure, ← hTargetMeasure, ← hDecomp,
    ENNReal.toReal_add
      (measure_ne_top (gamma.plan : Measure (Real × Real)) crossing)
      (measure_ne_top (gamma.plan : Measure (Real × Real)) targetLeft)]
  simp only [add_sub_cancel_right, crossing]

private theorem signedCumulative_measurable
    (mu nu : FiniteMeasure Real) :
    Measurable (signedCumulative mu nu) := by
  have hMuMonotone :
      Monotone (fun x : Real => ((mu : Measure Real) (Iic x)).toReal) := by
    intro a b hab
    exact ENNReal.toReal_mono
      (measure_ne_top (mu : Measure Real) (Iic b))
      (measure_mono (Iic_subset_Iic.mpr hab))
  have hNuMonotone :
      Monotone (fun x : Real => ((nu : Measure Real) (Iic x)).toReal) := by
    intro a b hab
    exact ENNReal.toReal_mono
      (measure_ne_top (nu : Measure Real) (Iic b))
      (measure_mono (Iic_subset_Iic.mpr hab))
  exact hMuMonotone.measurable.sub hNuMonotone.measurable

private theorem measure_Iic_pos_ae
    (eta : Measure Real) [IsFiniteMeasure eta] :
    ∀ᵐ x ∂eta, 0 < eta (Iic x) := by
  let bad : Set Real := {x | eta (Iic x) = 0}
  have hCumulativeMonotone :
      Monotone (fun x : Real => eta (Iic x)) := by
    intro a b hab
    exact measure_mono (Iic_subset_Iic.mpr hab)
  have hBadMeasurable : MeasurableSet bad := by
    change MeasurableSet
      ((fun x : Real => eta (Iic x)) ⁻¹' {(0 : ENNReal)})
    exact hCumulativeMonotone.measurable
      (measurableSet_singleton (0 : ENNReal))
  let ordered : Set (Real × Real) :=
    (bad ×ˢ bad) ∩ {p | p.2 <= p.1}
  have hOrderedMeasurable : MeasurableSet ordered :=
    (hBadMeasurable.prod hBadMeasurable).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hOrderedZero : eta.prod eta ordered = 0 := by
    rw [Measure.measure_prod_null hOrderedMeasurable]
    refine Filter.Eventually.of_forall fun x => ?_
    change eta (Prod.mk x ⁻¹' ordered) = 0
    by_cases hx : x ∈ bad
    · apply measure_mono_null
        (t := Iic x)
        (fun y hy => hy.2)
      exact hx
    · have hSection :
          Prod.mk x ⁻¹' ordered = (∅ : Set Real) := by
        ext y
        simp [ordered, hx]
      rw [hSection, measure_empty]
  let reversed : Set (Real × Real) := Prod.swap ⁻¹' ordered
  have hReversedZero : eta.prod eta reversed = 0 := by
    change eta.prod eta (Prod.swap ⁻¹' ordered) = 0
    rw [← Measure.map_apply measurable_swap hOrderedMeasurable,
      Measure.prod_swap]
    exact hOrderedZero
  have hCover : bad ×ˢ bad ⊆ ordered ∪ reversed := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    rcases le_total b a with hba | hab
    · exact Or.inl ⟨⟨ha, hb⟩, hba⟩
    · apply Or.inr
      exact ⟨⟨hb, ha⟩, hab⟩
  have hBadProdZero : eta.prod eta (bad ×ˢ bad) = 0 :=
    measure_mono_null hCover
      (measure_union_null hOrderedZero hReversedZero)
  have hBadMulZero : eta bad * eta bad = 0 := by
    simpa only [Measure.prod_prod] using hBadProdZero
  have hBadZero : eta bad = 0 := by
    rcases mul_eq_zero.mp hBadMulZero with h | h
    · exact h
    · exact h
  apply ae_iff.mpr
  simpa only [bad, not_lt, nonpos_iff_eq_zero] using hBadZero

/-- If a finite coupling moves strictly forward almost everywhere, then its
source signed-cumulative level is positive source-almost everywhere. -/
theorem signedCumulativePositiveAeOfStrictForwardPlan
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (hStrict :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.1 < z.2) :
    ∀ᵐ x ∂(mu : Measure Real), 0 < signedCumulative mu nu x := by
  let archAt (q : Rat) : Set (Real × Real) :=
    {z | z.1 < (q : Real) ∧ (q : Real) < z.2}
  have hArchAtMeasurable (q : Rat) : MeasurableSet (archAt q) :=
    (measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_lt measurable_const measurable_snd)
  have hForward : IsForwardPlan gamma :=
    hStrict.mono fun _ hz => hz.le
  have hAtRational (q : Rat) :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)),
        z ∈ archAt q ->
          0 <
            (gamma.plan : Measure (Real × Real))
              {w | w.1 <= z.1 ∧ z.1 < w.2} := by
    let eta : Measure Real :=
      Measure.map Prod.fst
        ((gamma.plan : Measure (Real × Real)).restrict (archAt q))
    have hEtaPositive :
        ∀ᵐ x ∂eta, 0 < eta (Iic x) :=
      measure_Iic_pos_ae eta
    have hPullback :
        ∀ᵐ z ∂((gamma.plan : Measure (Real × Real)).restrict (archAt q)),
          0 < eta (Iic z.1) := by
      apply ae_of_ae_map
        (μ :=
          (gamma.plan : Measure (Real × Real)).restrict (archAt q))
        (p := fun x : Real => 0 < eta (Iic x))
        measurable_fst.aemeasurable
      simpa only [eta] using hEtaPositive
    apply (ae_restrict_iff' (hArchAtMeasurable q)).mp
    filter_upwards
      [hPullback, ae_restrict_mem (hArchAtMeasurable q)] with z hz hArch
    have hSubset :
        Prod.fst ⁻¹' Iic z.1 ∩ archAt q ⊆
          {w : Real × Real | w.1 <= z.1 ∧ z.1 < w.2} := by
      intro w hw
      exact ⟨hw.1, hArch.1.trans hw.2.2⟩
    have hMeasureLe :
        eta (Iic z.1) <=
          (gamma.plan : Measure (Real × Real))
            {w | w.1 <= z.1 ∧ z.1 < w.2} := by
      change
        Measure.map Prod.fst
            ((gamma.plan : Measure (Real × Real)).restrict (archAt q))
            (Iic z.1) <=
          (gamma.plan : Measure (Real × Real))
            {w | w.1 <= z.1 ∧ z.1 < w.2}
      rw [Measure.map_apply measurable_fst measurableSet_Iic,
        Measure.restrict_apply
          (measurableSet_Iic.preimage measurable_fst)]
      exact measure_mono hSubset
    exact hz.trans_le hMeasureLe
  have hAllRationals :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)),
        ∀ q : Rat,
          z ∈ archAt q ->
            0 <
              (gamma.plan : Measure (Real × Real))
                {w | w.1 <= z.1 ∧ z.1 < w.2} :=
    ae_all_iff.mpr hAtRational
  have hCrossingPositive :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)),
        0 <
          (gamma.plan : Measure (Real × Real))
            {w | w.1 <= z.1 ∧ z.1 < w.2} := by
    filter_upwards [hStrict, hAllRationals] with z hz hAll
    obtain ⟨q, hzq, hqz⟩ := exists_rat_btwn hz
    exact hAll q ⟨hzq, hqz⟩
  have hPlanPositive :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)),
        0 < signedCumulative mu nu z.1 := by
    filter_upwards [hCrossingPositive] with z hz
    rw [signedCumulative_eq_forwardCrossing gamma hForward]
    exact ENNReal.toReal_pos hz.ne'
      (measure_ne_top (gamma.plan : Measure (Real × Real))
        {w | w.1 <= z.1 ∧ z.1 < w.2})
  have hPositiveMeasurable :
      MeasurableSet {x : Real | 0 < signedCumulative mu nu x} :=
    measurableSet_lt measurable_const
      (signedCumulative_measurable mu nu)
  have hMapPositive :
      ∀ᵐ x ∂Measure.map Prod.fst
          (gamma.plan : Measure (Real × Real)),
        0 < signedCumulative mu nu x :=
    (ae_map_iff measurable_fst.aemeasurable hPositiveMeasurable).mpr
      hPlanPositive
  simpa only [(measurePreservingFst gamma).map_eq] using hMapPositive

/-- The positive-level half of Juillet's regular-level input: a Juillet
excursion coupling of atomless mutually singular marginals in stochastic
order has positive signed-cumulative level at source-almost every point. -/
theorem juilletPositiveLevelsAe
    {mu nu : FiniteMeasure Real}
    {gamma : FiniteCoupling mu nu}
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (hExcursion : IsJuilletExcursionPlan mu nu gamma.plan) :
    ∀ᵐ x ∂(mu : Measure Real), 0 < signedCumulative mu nu x := by
  obtain ⟨S, _hSMeasurable, hFull, hStrict, _hMonotone⟩ :=
    existsStrictMonotoneArchSupportOfJuilletExcursionPlan
      hSingular hAtomless hOrder hExcursion
  apply signedCumulativePositiveAeOfStrictForwardPlan gamma
  filter_upwards [hFull] with z hz
  exact hStrict hz

end ConcaveOTLimit

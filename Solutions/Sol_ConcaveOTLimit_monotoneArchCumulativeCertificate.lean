import Theorems.Thm_ConcaveOTLimit_monotoneArchPrefixCut
import Theorems.Thm_ConcaveOTLimit_signedCumulativeLeLeftOfAtomlessAt

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

private theorem sourceFiberNull
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (hAtomless : IsAtomlessFinite mu) (c : Real) :
    (gamma.plan : Measure (Real × Real)) {z | z.1 = c} = 0 := by
  calc
    (gamma.plan : Measure (Real × Real)) {z | z.1 = c} =
        Measure.map Prod.fst
          (gamma.plan : Measure (Real × Real)) {c} := by
      rw [Measure.map_apply measurable_fst (measurableSet_singleton c)]
      rfl
    _ = (mu : Measure Real) {c} := by
      rw [(measurePreservingFst gamma).map_eq]
    _ = 0 := hAtomless c

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
    change
      (z.1 <= c ∧ z.2 <= c) = (z.2 <= c)
    apply propext
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨hz.trans h, h⟩
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

private theorem signedCumulativeLeft_eq_forwardCrossing
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (hForward : IsForwardPlan gamma) (c : Real) :
    signedCumulativeLeft mu nu c =
      ((gamma.plan : Measure (Real × Real))
        {z | z.1 < c ∧ c <= z.2}).toReal := by
  let sourceLeft : Set (Real × Real) := {z | z.1 < c}
  let targetLeft : Set (Real × Real) := {z | z.2 < c}
  let crossing : Set (Real × Real) := {z | z.1 < c ∧ c <= z.2}
  have hTargetMeasurable : MeasurableSet targetLeft :=
    measurableSet_lt measurable_snd measurable_const
  have hSourceDiff : sourceLeft \ targetLeft = crossing := by
    ext z
    simp only [sourceLeft, targetLeft, crossing, mem_diff, mem_setOf_eq,
      not_lt]
  have hSourceMeasure :
      (gamma.plan : Measure (Real × Real)) sourceLeft =
        (mu : Measure Real) (Iio c) := by
    calc
      (gamma.plan : Measure (Real × Real)) sourceLeft =
          Measure.map Prod.fst
            (gamma.plan : Measure (Real × Real)) (Iio c) := by
        rw [Measure.map_apply measurable_fst measurableSet_Iio]
        rfl
      _ = (mu : Measure Real) (Iio c) := by
        rw [(measurePreservingFst gamma).map_eq]
  have hTargetMeasure :
      (gamma.plan : Measure (Real × Real)) targetLeft =
        (nu : Measure Real) (Iio c) := by
    calc
      (gamma.plan : Measure (Real × Real)) targetLeft =
          Measure.map Prod.snd
            (gamma.plan : Measure (Real × Real)) (Iio c) := by
        rw [Measure.map_apply measurable_snd measurableSet_Iio]
        rfl
      _ = (nu : Measure Real) (Iio c) := by
        rw [(measurePreservingSnd gamma).map_eq]
  have hTargetInter :
      (gamma.plan : Measure (Real × Real))
          (sourceLeft ∩ targetLeft) =
        (gamma.plan : Measure (Real × Real)) targetLeft := by
    apply measure_congr
    filter_upwards [hForward] with z hz
    change
      (z.1 < c ∧ z.2 < c) = (z.2 < c)
    apply propext
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨hz.trans_lt h, h⟩
  have hDecomp :
      (gamma.plan : Measure (Real × Real)) crossing +
          (gamma.plan : Measure (Real × Real)) targetLeft =
        (gamma.plan : Measure (Real × Real)) sourceLeft := by
    rw [← hTargetInter, ← hSourceDiff]
    exact measure_diff_add_inter sourceLeft hTargetMeasurable
  rw [signedCumulativeLeft, ← hSourceMeasure, ← hTargetMeasure,
    ← hDecomp,
    ENNReal.toReal_add
      (measure_ne_top (gamma.plan : Measure (Real × Real)) crossing)
      (measure_ne_top (gamma.plan : Measure (Real × Real)) targetLeft)]
  simp only [add_sub_cancel_right, crossing]

theorem solution
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hForward : IsForwardPlan gamma)
    (S : Set (Real × Real))
    (hFull : IsSupported gamma S)
    (hMonotone : IsMonotoneArchSet S)
    {x y : Real}
    (hArch : (x, y) ∈ S)
    (hxy : x < y) :
    (∀ t ∈ Ioo x y,
      signedCumulative mu nu x <= signedCumulative mu nu t) ∧
      (y, signedCumulative mu nu x) ∈
        generalizedCumulativeGraph mu nu := by
  have hSourceNeX :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.1 ≠ x := by
    apply ae_iff.mpr
    simpa only [not_ne_iff] using sourceFiberNull gamma hAtomless x
  have hSourceNeY :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.1 ≠ y := by
    apply ae_iff.mpr
    simpa only [not_ne_iff] using sourceFiberNull gamma hAtomless y
  have hEquation15 :=
    monotoneArchEquation15 gamma.plan S hFull hMonotone hArch hxy
  have hEquation15FirstAvoid :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)),
        z ∉ (Icc x y)ᶜ ×ˢ Ioo x y := by
    simpa only [ae_iff, Classical.not_not, setOf_mem_eq] using
      hEquation15.1
  have hEquation15SecondAvoid :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)),
        z ∉ Ioo x y ×ˢ (Icc x y)ᶜ := by
    simpa only [ae_iff, Classical.not_not, setOf_mem_eq] using
      hEquation15.2
  constructor
  · intro t ht
    have hPrefix :=
      monotoneArchPrefixCut gamma.plan S hFull hMonotone hArch ht
    have hPrefixAvoid :
        ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)),
          z ∉ (Icc x t)ᶜ ×ˢ Ioc x t := by
      simpa only [ae_iff, Classical.not_not, setOf_mem_eq] using hPrefix
    rw [signedCumulative_eq_forwardCrossing gamma hForward x,
      signedCumulative_eq_forwardCrossing gamma hForward t]
    apply ENNReal.toReal_mono
      (measure_ne_top (gamma.plan : Measure (Real × Real))
        {z | z.1 <= t ∧ t < z.2})
    apply measure_mono_ae
    filter_upwards [hPrefixAvoid, hSourceNeX] with z hzPrefix hzNeX
    intro hzCrossing
    refine ⟨hzCrossing.1.trans ht.1.le, ?_⟩
    by_contra hNotAbove
    apply hzPrefix
    constructor
    · intro hzInside
      exact hzNeX (le_antisymm hzCrossing.1 hzInside.1)
    · exact ⟨hzCrossing.2, le_of_not_gt hNotAbove⟩
  · have hCumulativeYLeX :
        signedCumulative mu nu y <= signedCumulative mu nu x := by
      rw [signedCumulative_eq_forwardCrossing gamma hForward y,
        signedCumulative_eq_forwardCrossing gamma hForward x]
      apply ENNReal.toReal_mono
        (measure_ne_top (gamma.plan : Measure (Real × Real))
          {z | z.1 <= x ∧ x < z.2})
      apply measure_mono_ae
      filter_upwards [hEquation15SecondAvoid, hSourceNeY] with
        z hzEquation15 hzNeY
      intro hzCrossing
      refine ⟨?_, hxy.trans hzCrossing.2⟩
      by_contra hNotLeft
      apply hzEquation15
      constructor
      · exact ⟨lt_of_not_ge hNotLeft,
          lt_of_le_of_ne hzCrossing.1 hzNeY⟩
      · intro hzInside
        exact (not_le_of_gt hzCrossing.2) hzInside.2
    have hCumulativeXLeLeftY :
        signedCumulative mu nu x <= signedCumulativeLeft mu nu y := by
      rw [signedCumulative_eq_forwardCrossing gamma hForward x,
        signedCumulativeLeft_eq_forwardCrossing gamma hForward y]
      apply ENNReal.toReal_mono
        (measure_ne_top (gamma.plan : Measure (Real × Real))
          {z | z.1 < y ∧ y <= z.2})
      apply measure_mono_ae
      filter_upwards [hEquation15FirstAvoid, hSourceNeX] with
        z hzEquation15 hzNeX
      intro hzCrossing
      refine ⟨hzCrossing.1.trans_lt hxy, ?_⟩
      by_contra hNotAbove
      apply hzEquation15
      constructor
      · intro hzInside
        exact hzNeX (le_antisymm hzCrossing.1 hzInside.1)
      · exact ⟨hzCrossing.2, lt_of_not_ge hNotAbove⟩
    have hCumulativeYLeLeftY :
        signedCumulative mu nu y <= signedCumulativeLeft mu nu y :=
      signedCumulativeLeLeftOfAtomlessAt mu nu y (hAtomless y)
    change
      signedCumulative mu nu x ∈
        uIcc (signedCumulativeLeft mu nu y)
          (signedCumulative mu nu y)
    rw [uIcc_comm, uIcc_of_le hCumulativeYLeLeftY]
    exact ⟨hCumulativeYLeX, hCumulativeXLeLeftY⟩

import Theorems.Thm_ConcaveOTLimit_weakRayCoordinateAtomlessnessProducer

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal

noncomputable section

namespace ConcaveOTLimit

private def rationalLevel (j : Nat) : Rat :=
  (Encodable.decode (α := Rat) j).getD 0

/-- The left quantile at a rational mass level, formed as an infimum over
rational spatial cutoffs. Using `EReal` makes the infimum total even for
levels outside the mass range. -/
private def kernelAtomQuantileE
    {A : Type*} [MeasurableSpace A]
    (kappa : Kernel A Real) (q : Rat) (a : A) : EReal :=
  ⨅ r : Rat,
    if (Real.toNNReal q : ENNReal) <= kappa a (Iic (r : Real)) then
      ((r : Real) : EReal)
    else
      ⊤

private def kernelAtomQuantile
    {A : Type*} [MeasurableSpace A]
    (kappa : Kernel A Real) (q : Rat) (a : A) : Real :=
  (kernelAtomQuantileE kappa q a).toReal

private theorem measurable_kernelAtomQuantile
    {A : Type*} [MeasurableSpace A]
    (kappa : Kernel A Real) (q : Rat) :
    Measurable (kernelAtomQuantile kappa q) := by
  apply Measurable.ereal_toReal
  apply Measurable.iInf
  intro r
  exact Measurable.ite
    (measurableSet_le measurable_const
      (kappa.measurable_coe measurableSet_Iic))
    measurable_const measurable_const

private theorem kernelAtomQuantileE_eq_of_mem_jump
    {A : Type*} [MeasurableSpace A]
    (kappa : Kernel A Real) (a : A) (t : Real) (q : Rat)
    (hlower :
      kappa a (Iio t) < (Real.toNNReal q : ENNReal))
    (hupper :
      (Real.toNNReal q : ENNReal) < kappa a (Iic t)) :
    kernelAtomQuantileE kappa q a = (t : EReal) := by
  apply le_antisymm
  · apply EReal.le_of_forall_lt_iff_le.mp
    intro z htz
    obtain ⟨r, htr, hrz⟩ :=
      exists_rat_btwn (EReal.coe_lt_coe_iff.mp htz)
    have hlevel :
        (Real.toNNReal q : ENNReal) <=
          kappa a (Iic (r : Real)) :=
      hupper.le.trans
        (measure_mono (Iic_subset_Iic.mpr htr.le))
    calc
      kernelAtomQuantileE kappa q a <=
          if (Real.toNNReal q : ENNReal) <=
              kappa a (Iic (r : Real)) then
            ((r : Real) : EReal)
          else
            ⊤ := iInf_le _ r
      _ = ((r : Real) : EReal) := if_pos hlevel
      _ <= (z : EReal) :=
        EReal.coe_le_coe_iff.mpr hrz.le
  · apply le_iInf
    intro r
    split_ifs with hlevel
    · apply EReal.coe_le_coe_iff.mpr
      apply le_of_not_gt
      intro hrt
      exact (not_le_of_gt hlower)
        (hlevel.trans
          (measure_mono (Iic_subset_Iio.mpr hrt)))
    · exact le_top

private theorem kernelAtomQuantile_eq_of_mem_jump
    {A : Type*} [MeasurableSpace A]
    (kappa : Kernel A Real) (a : A) (t : Real) (q : Rat)
    (hlower :
      kappa a (Iio t) < (Real.toNNReal q : ENNReal))
    (hupper :
      (Real.toNNReal q : ENNReal) < kappa a (Iic t)) :
    kernelAtomQuantile kappa q a = t := by
  rw [kernelAtomQuantile,
    kernelAtomQuantileE_eq_of_mem_jump kappa a t q hlower hupper]
  exact EReal.toReal_coe t

/-- The atoms of every finite real-valued kernel admit a countable
measurable enumeration. No countable-generation assumption on the kernel's
base space is needed. -/
theorem finiteKernel_hasMeasurableAtomEnumeration
    {A : Type*} [MeasurableSpace A]
    (kappa : Kernel A Real) [IsFiniteKernel kappa] :
    HasMeasurableAtomEnumeration kappa := by
  refine ⟨fun j => kernelAtomQuantile kappa (rationalLevel j), ?_, ?_⟩
  · intro j
    exact measurable_kernelAtomQuantile kappa (rationalLevel j)
  · intro a t hatom
    have hjump : kappa a (Iio t) < kappa a (Iic t) := by
      rw [← Iio_union_right,
        measure_union (by simp) (measurableSet_singleton t)]
      exact ENNReal.lt_add_right (measure_ne_top (kappa a) _) hatom
    obtain ⟨q, _hq_nonneg, hlower, hupper⟩ :=
      ENNReal.lt_iff_exists_rat_btwn.mp hjump
    obtain ⟨j, hj⟩ :=
      Encodable.surjective_decode_getD Rat 0 q
    refine ⟨j, ?_⟩
    change kernelAtomQuantile kappa (rationalLevel j) a = t
    rw [show rationalLevel j = q by exact hj]
    exact kernelAtomQuantile_eq_of_mem_jump
      kappa a t q hlower hupper

/-- Countably Lipschitz maximal-ray geometry forces atomless conditional
ray coordinates. The measurable atom enumeration needed by the geometric
argument is supplied for free by the quantile construction above. -/
theorem countablyLipschitzRayCoordinateAtomlessPremise
    {n : Nat} (mu : FiniteMeasure (Euclidean n))
    (Gamma : Set (Euclidean n × Euclidean n))
    (hRegularity :
      RayRegularityHypotheses
        (mu : Measure (Euclidean n)) Gamma)
    (pi : transportSet Gamma -> OrientedOpenRay n)
    (defaultRay : OrientedOpenRay n) :
    CountablyLipschitzRayCoordinateAtomlessPremise
      mu Gamma hRegularity pi defaultRay := by
  apply
    countablyLipschitzRayCoordinateAtomlessPremise_of_atomEnumeration
      mu Gamma hRegularity pi defaultRay
  exact finiteKernel_hasMeasurableAtomEnumeration _

end ConcaveOTLimit

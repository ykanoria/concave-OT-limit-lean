import Definitions.Def_JuilletMassClock
import Mathlib.Topology.MetricSpace.Lipschitz

open MeasureTheory Set

namespace ConcaveOTLimit

/-- The signed cumulative function is a `1`-Lipschitz function of the
cumulative total-mass clock. -/
theorem existsSignedCumulativeLipschitzMassClockFactor
    (mu nu : FiniteMeasure Real) :
    Monotone (cumulativeMassClock mu nu) /\
      (forall x y : Real,
        |signedCumulative mu nu y - signedCumulative mu nu x| <=
          |cumulativeMassClock mu nu y -
            cumulativeMassClock mu nu x|) /\
      exists g : Real -> Real,
        LipschitzWith 1 g /\
          forall x : Real,
            g (cumulativeMassClock mu nu x) =
              signedCumulative mu nu x := by
  have hClockMonotone : Monotone (cumulativeMassClock mu nu) := by
    intro x y hxy
    exact add_le_add
      (measureReal_mono (Iic_subset_Iic.mpr hxy))
      (measureReal_mono (Iic_subset_Iic.mpr hxy))
  have hOrdered
      {x y : Real} (hxy : x <= y) :
      |signedCumulative mu nu y - signedCumulative mu nu x| <=
        |cumulativeMassClock mu nu y -
          cumulativeMassClock mu nu x| := by
    have hMu :
        0 <=
          (mu : Measure Real).real (Iic y) -
            (mu : Measure Real).real (Iic x) :=
      sub_nonneg.mpr
        (measureReal_mono (Iic_subset_Iic.mpr hxy))
    have hNu :
        0 <=
          (nu : Measure Real).real (Iic y) -
            (nu : Measure Real).real (Iic x) :=
      sub_nonneg.mpr
        (measureReal_mono (Iic_subset_Iic.mpr hxy))
    calc
      |signedCumulative mu nu y - signedCumulative mu nu x| =
          |((mu : Measure Real).real (Iic y) -
              (mu : Measure Real).real (Iic x)) -
            ((nu : Measure Real).real (Iic y) -
              (nu : Measure Real).real (Iic x))| := by
        unfold signedCumulative
        simp only [Measure.real]
        congr 1
        ring
      _ <=
          |(mu : Measure Real).real (Iic y) -
              (mu : Measure Real).real (Iic x)| +
            |(nu : Measure Real).real (Iic y) -
              (nu : Measure Real).real (Iic x)| :=
        abs_sub _ _
      _ =
          ((mu : Measure Real).real (Iic y) -
              (mu : Measure Real).real (Iic x)) +
            ((nu : Measure Real).real (Iic y) -
              (nu : Measure Real).real (Iic x)) := by
        rw [abs_of_nonneg hMu, abs_of_nonneg hNu]
      _ =
          cumulativeMassClock mu nu y -
            cumulativeMassClock mu nu x := by
        unfold cumulativeMassClock
        ring
      _ =
          |cumulativeMassClock mu nu y -
            cumulativeMassClock mu nu x| := by
        symm
        exact abs_of_nonneg
          (sub_nonneg.mpr (hClockMonotone hxy))
  have hSharp :
      forall x y : Real,
        |signedCumulative mu nu y - signedCumulative mu nu x| <=
          |cumulativeMassClock mu nu y -
            cumulativeMassClock mu nu x| := by
    intro x y
    rcases le_total x y with hxy | hyx
    · exact hOrdered hxy
    · simpa only [abs_sub_comm] using
        (hOrdered (x := y) (y := x) hyx)
  let clockFactor : Real -> Real :=
    fun t =>
      signedCumulative mu nu
        (Function.invFun (cumulativeMassClock mu nu) t)
  have hClockFactor
      (x : Real) :
      clockFactor (cumulativeMassClock mu nu x) =
        signedCumulative mu nu x := by
    let representative :=
      Function.invFun (cumulativeMassClock mu nu)
        (cumulativeMassClock mu nu x)
    have hRepresentative :
        cumulativeMassClock mu nu representative =
          cumulativeMassClock mu nu x :=
      Function.invFun_eq ⟨x, rfl⟩
    have hLe :
        |signedCumulative mu nu representative -
            signedCumulative mu nu x| <= 0 := by
      simpa only [hRepresentative, sub_self, abs_zero] using
        (hSharp x representative)
    have hEq :
        signedCumulative mu nu representative =
          signedCumulative mu nu x := by
      apply sub_eq_zero.mp
      apply abs_eq_zero.mp
      exact le_antisymm hLe (abs_nonneg _)
    simpa only [clockFactor, representative] using hEq
  have hLipschitzOn :
      LipschitzOnWith 1 clockFactor
        (Set.range (cumulativeMassClock mu nu)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    rcases ha with ⟨x, rfl⟩
    rcases hb with ⟨y, rfl⟩
    rw [hClockFactor x, hClockFactor y]
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    simpa only [abs_sub_comm] using hSharp x y
  obtain ⟨g, hgLipschitz, hgEq⟩ := hLipschitzOn.extend_real
  refine ⟨hClockMonotone, hSharp, g, hgLipschitz, ?_⟩
  intro x
  calc
    g (cumulativeMassClock mu nu x) =
        clockFactor (cumulativeMassClock mu nu x) :=
      (hgEq ⟨x, rfl⟩).symm
    _ = signedCumulative mu nu x := hClockFactor x

end ConcaveOTLimit

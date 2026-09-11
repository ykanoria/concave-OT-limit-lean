import Definitions.Def_JuilletCanonicalRoutes
import Mathlib.Topology.EMetricSpace.BoundedVariation

open MeasureTheory Set

namespace ConcaveOTLimit

/-- The signed cumulative function of two finite measures has globally
bounded variation. -/
theorem signedCumulativeBoundedVariation
    (mu nu : FiniteMeasure Real) :
    BoundedVariationOn (signedCumulative mu nu) Set.univ := by
  let Fmu : Real -> Real :=
    fun x => ((mu : Measure Real) (Iic x)).toReal
  let Fnu : Real -> Real :=
    fun x => ((nu : Measure Real) (Iic x)).toReal
  have hMuMonotone : Monotone Fmu := by
    intro a b hab
    exact ENNReal.toReal_mono
      (measure_ne_top (mu : Measure Real) (Iic b))
      (measure_mono (Iic_subset_Iic.mpr hab))
  have hNuMonotone : Monotone Fnu := by
    intro a b hab
    exact ENNReal.toReal_mono
      (measure_ne_top (nu : Measure Real) (Iic b))
      (measure_mono (Iic_subset_Iic.mpr hab))
  have hMuNonneg (x : Real) : 0 <= Fmu x :=
    ENNReal.toReal_nonneg
  have hNuNonneg (x : Real) : 0 <= Fnu x :=
    ENNReal.toReal_nonneg
  have hMuLe (x : Real) :
      Fmu x <= ((mu : Measure Real) Set.univ).toReal := by
    exact ENNReal.toReal_mono
      (measure_ne_top (mu : Measure Real) Set.univ)
      (measure_mono (subset_univ (Iic x)))
  have hNuLe (x : Real) :
      Fnu x <= ((nu : Measure Real) Set.univ).toReal := by
    exact ENNReal.toReal_mono
      (measure_ne_top (nu : Measure Real) Set.univ)
      (measure_mono (subset_univ (Iic x)))
  unfold BoundedVariationOn
  refine ne_top_of_le_ne_top
    (b :=
      ENNReal.ofReal ((mu : Measure Real) Set.univ).toReal +
        ENNReal.ofReal ((nu : Measure Real) Set.univ).toReal)
    (by finiteness) ?_
  apply iSup_le
  rintro ⟨n, ⟨u, hu, _⟩⟩
  have hMuInc (i : Nat) :
      0 <= Fmu (u (i + 1)) - Fmu (u i) :=
    sub_nonneg.mpr (hMuMonotone (hu (Nat.le_succ i)))
  have hNuInc (i : Nat) :
      0 <= Fnu (u (i + 1)) - Fnu (u i) :=
    sub_nonneg.mpr (hNuMonotone (hu (Nat.le_succ i)))
  calc
    (∑ i ∈ Finset.range n,
        edist (signedCumulative mu nu (u (i + 1)))
          (signedCumulative mu nu (u i))) <=
        ∑ i ∈ Finset.range n,
          (ENNReal.ofReal (Fmu (u (i + 1)) - Fmu (u i)) +
            ENNReal.ofReal (Fnu (u (i + 1)) - Fnu (u i))) := by
      apply Finset.sum_le_sum
      intro i hi
      change
        edist (Fmu (u (i + 1)) - Fnu (u (i + 1)))
            (Fmu (u i) - Fnu (u i)) <=
          ENNReal.ofReal (Fmu (u (i + 1)) - Fmu (u i)) +
            ENNReal.ofReal (Fnu (u (i + 1)) - Fnu (u i))
      rw [edist_dist, Real.dist_eq]
      calc
        ENNReal.ofReal
              |(Fmu (u (i + 1)) - Fnu (u (i + 1))) -
                (Fmu (u i) - Fnu (u i))| =
            ENNReal.ofReal
              |(Fmu (u (i + 1)) - Fmu (u i)) -
                (Fnu (u (i + 1)) - Fnu (u i))| := by
          congr 2
          ring
        _ <= ENNReal.ofReal
              ((Fmu (u (i + 1)) - Fmu (u i)) +
                (Fnu (u (i + 1)) - Fnu (u i))) := by
          apply ENNReal.ofReal_le_ofReal
          calc
            |(Fmu (u (i + 1)) - Fmu (u i)) -
                (Fnu (u (i + 1)) - Fnu (u i))| <=
                |Fmu (u (i + 1)) - Fmu (u i)| +
                  |Fnu (u (i + 1)) - Fnu (u i)| :=
              abs_sub _ _
            _ = (Fmu (u (i + 1)) - Fmu (u i)) +
                (Fnu (u (i + 1)) - Fnu (u i)) := by
              rw [abs_of_nonneg (hMuInc i), abs_of_nonneg (hNuInc i)]
        _ = ENNReal.ofReal (Fmu (u (i + 1)) - Fmu (u i)) +
              ENNReal.ofReal (Fnu (u (i + 1)) - Fnu (u i)) :=
          ENNReal.ofReal_add (hMuInc i) (hNuInc i)
    _ = (∑ i ∈ Finset.range n,
          ENNReal.ofReal (Fmu (u (i + 1)) - Fmu (u i))) +
        ∑ i ∈ Finset.range n,
          ENNReal.ofReal (Fnu (u (i + 1)) - Fnu (u i)) := by
      rw [Finset.sum_add_distrib]
    _ = ENNReal.ofReal (Fmu (u n) - Fmu (u 0)) +
        ENNReal.ofReal (Fnu (u n) - Fnu (u 0)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg
          (fun i _ => hMuInc i),
        ← ENNReal.ofReal_sum_of_nonneg
          (fun i _ => hNuInc i),
        Finset.sum_range_sub (fun i => Fmu (u i)),
        Finset.sum_range_sub (fun i => Fnu (u i))]
    _ <= ENNReal.ofReal ((mu : Measure Real) Set.univ).toReal +
        ENNReal.ofReal ((nu : Measure Real) Set.univ).toReal := by
      apply add_le_add <;> apply ENNReal.ofReal_le_ofReal
      · exact (sub_le_self _ (hMuNonneg (u 0))).trans (hMuLe (u n))
      · exact (sub_le_self _ (hNuNonneg (u 0))).trans (hNuLe (u n))

end ConcaveOTLimit

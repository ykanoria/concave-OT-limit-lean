import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Topology.MetricSpace.Lipschitz

open Set

namespace ConcaveOTLimit

/-- The pointwise infimum of a nonempty, equi-Lipschitz family of
real-valued functions is Lipschitz wherever the family is pointwise bounded
below. -/
theorem lipschitzOnWith_sInf_range
    {X I : Type*} [PseudoMetricSpace X] [Nonempty I]
    (C : NNReal) (f : I → X → Real) (s : Set X)
    (hLipschitz : ∀ i, LipschitzOnWith C (f i) s)
    (hBounded :
      ∀ x ∈ s, BddBelow (Set.range fun i => f i x)) :
    LipschitzOnWith C
      (fun x => sInf (Set.range fun i => f i x)) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let infimum : X → Real :=
    fun z => sInf (Set.range fun i => f i z)
  have hInfimumLe (z : X) (hz : z ∈ s) (i : I) :
      infimum z ≤ f i z :=
    csInf_le (hBounded z hz) ⟨i, rfl⟩
  have hxy :
      infimum x - (C : Real) * dist x y ≤ infimum y := by
    apply le_csInf (Set.range_nonempty _)
    intro value hValue
    obtain ⟨i, rfl⟩ := hValue
    have hOneSided :
        f i x - f i y ≤ (C : Real) * dist x y := by
      calc
        f i x - f i y ≤ |f i x - f i y| := le_abs_self _
        _ = dist (f i x) (f i y) := by rw [Real.dist_eq]
        _ ≤ (C : Real) * dist x y :=
          (hLipschitz i).dist_le_mul x hx y hy
    linarith [hInfimumLe x hx i]
  have hyx :
      infimum y - (C : Real) * dist x y ≤ infimum x := by
    apply le_csInf (Set.range_nonempty _)
    intro value hValue
    obtain ⟨i, rfl⟩ := hValue
    have hOneSided :
        f i y - f i x ≤ (C : Real) * dist x y := by
      calc
        f i y - f i x ≤ |f i y - f i x| := le_abs_self _
        _ = dist (f i y) (f i x) := by rw [Real.dist_eq]
        _ ≤ (C : Real) * dist y x :=
          (hLipschitz i).dist_le_mul y hy x hx
        _ = (C : Real) * dist x y := by rw [dist_comm y x]
    linarith [hInfimumLe y hy i]
  change dist (infimum x) (infimum y) ≤ (C : Real) * dist x y
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

end ConcaveOTLimit

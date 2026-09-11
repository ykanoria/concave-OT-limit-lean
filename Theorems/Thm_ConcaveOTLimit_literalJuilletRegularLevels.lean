import Definitions.Def_LiteralJuilletExcursion
import Theorems.Thm_ConcaveOTLimit_completedGraphLevelFiniteAe

open MeasureTheory Set

namespace ConcaveOTLimit

/-- A completed-graph hit cannot be both a strict entrance and a strict exit. -/
theorem goodIncreasingCrossing_not_goodDecreasingCrossing
    (mu nu : FiniteMeasure Real) (x h : Real)
    (hIncreasing : IsGoodIncreasingCrossing mu nu x h)
    (hDecreasing : IsGoodDecreasingCrossing mu nu x h) :
    False := by
  obtain ⟨_hGraphIncreasing, epsilonIncreasing,
      hEpsilonIncreasing, hIncreasingLocal⟩ := hIncreasing
  obtain ⟨_hGraphDecreasing, epsilonDecreasing,
      hEpsilonDecreasing, hDecreasingLocal⟩ := hDecreasing
  let delta := min epsilonIncreasing epsilonDecreasing / 2
  have hMinPositive :
      0 < min epsilonIncreasing epsilonDecreasing :=
    lt_min hEpsilonIncreasing hEpsilonDecreasing
  have hDeltaPositive : 0 < delta := by
    dsimp only [delta]
    positivity
  have hDeltaIncreasing : delta < epsilonIncreasing := by
    dsimp only [delta]
    nlinarith [min_le_left epsilonIncreasing epsilonDecreasing]
  have hDeltaDecreasing : delta < epsilonDecreasing := by
    dsimp only [delta]
    nlinarith [min_le_right epsilonIncreasing epsilonDecreasing]
  let x' := x + delta
  have hxIncreasing :
      x' ∈ Ioo (x - epsilonIncreasing) (x + epsilonIncreasing) := by
    constructor <;> dsimp only [x'] <;> linarith
  have hxDecreasing :
      x' ∈ Ioo (x - epsilonDecreasing) (x + epsilonDecreasing) := by
    constructor <;> dsimp only [x'] <;> linarith
  have hxNe : x' ≠ x := by
    dsimp only [x']
    linarith
  have hxGraph :
      (x', signedCumulative mu nu x') ∈
        generalizedCumulativeGraph mu nu := by
    change
      signedCumulative mu nu x' ∈
        uIcc (signedCumulativeLeft mu nu x')
          (signedCumulative mu nu x')
    exact right_mem_uIcc
  have hPositive :=
    hIncreasingLocal hxIncreasing hxNe hxGraph
  have hNegative :=
    hDecreasingLocal hxDecreasing hxNe hxGraph
  linarith

/-- The finite-and-regular completed-graph theorem supplies the exact regular
positive-level field used by the literal pairing data. -/
theorem isJuilletRegularPositiveLevel_ae
    (mu nu : FiniteMeasure Real)
    (hAtomless : IsAtomlessFinite mu) :
    ∀ᵐ h ∂(volume : Measure Real).restrict (Ioi 0),
      IsJuilletRegularPositiveLevel mu nu h := by
  filter_upwards
    [ae_restrict_of_ae
      (generalizedCumulativeGraphFiniteAndRegularAe
        mu nu hAtomless),
      ae_restrict_mem measurableSet_Ioi] with h hRegular hPositive
  refine ⟨hPositive, hRegular.1, ?_⟩
  intro x hx
  rcases hRegular.2 x hx with hIncreasing | hDecreasing
  · exact Or.inl
      ⟨hIncreasing,
        goodIncreasingCrossing_not_goodDecreasingCrossing
          mu nu x h hIncreasing⟩
  · exact Or.inr
      ⟨hDecreasing,
        fun hIncreasing =>
          goodIncreasingCrossing_not_goodDecreasingCrossing
            mu nu x h hIncreasing hDecreasing⟩

end ConcaveOTLimit

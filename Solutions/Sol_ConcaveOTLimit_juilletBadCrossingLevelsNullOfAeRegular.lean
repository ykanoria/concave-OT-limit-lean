import Definitions.Def_JuilletCanonicalRoutes

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    (mu nu : FiniteMeasure Real)
    (hAeRegular :
      ∀ᵐ h ∂(volume : Measure Real),
        ∀ z : Real,
          (z, h) ∈ generalizedCumulativeGraph mu nu ->
            IsGoodIncreasingCrossing mu nu z h ∨
              IsGoodDecreasingCrossing mu nu z h) :
    (volume : Measure Real)
      {h |
        ∃ z : Real,
          (z, h) ∈ generalizedCumulativeGraph mu nu ∧
            ¬ (IsGoodIncreasingCrossing mu nu z h ∨
              IsGoodDecreasingCrossing mu nu z h)} = 0 := by
  have hNotBad :
      ∀ᵐ h ∂(volume : Measure Real),
        h ∉
          {h |
            ∃ z : Real,
              (z, h) ∈ generalizedCumulativeGraph mu nu ∧
                ¬ (IsGoodIncreasingCrossing mu nu z h ∨
                  IsGoodDecreasingCrossing mu nu z h)} := by
    filter_upwards [hAeRegular] with h hRegular
    rintro ⟨z, hGraph, hNotGood⟩
    exact hNotGood (hRegular z hGraph)
  simpa only [not_not, setOf_mem_eq] using (ae_iff.mp hNotBad)

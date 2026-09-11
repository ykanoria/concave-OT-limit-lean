import Definitions.Def_ConcaveOTLimitModel

open MeasureTheory

open ConcaveOTLimit

theorem solution
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (remainder removed added gamma : FiniteMeasure (X × Y))
    (hDecomposition : remainder + removed = gamma)
    (hFirst : firstMarginal added = firstMarginal removed)
    (hSecond : secondMarginal added = secondMarginal removed) :
    firstMarginal (remainder + added) = firstMarginal gamma ∧
      secondMarginal (remainder + added) = secondMarginal gamma := by
  constructor
  · change
      (remainder + added).map Prod.fst = gamma.map Prod.fst
    change added.map Prod.fst = removed.map Prod.fst at hFirst
    rw [FiniteMeasure.map_add measurable_fst, hFirst,
      ← FiniteMeasure.map_add measurable_fst, hDecomposition]
  · change
      (remainder + added).map Prod.snd = gamma.map Prod.snd
    change added.map Prod.snd = removed.map Prod.snd at hSecond
    rw [FiniteMeasure.map_add measurable_snd, hSecond,
      ← FiniteMeasure.map_add measurable_snd, hDecomposition]

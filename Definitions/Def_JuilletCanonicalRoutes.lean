import Definitions.Def_ConcaveOTLimitModel

open MeasureTheory Set

namespace ConcaveOTLimit

/-- The cumulative function of the signed measure `mu - nu`. -/
def signedCumulative
    (mu nu : FiniteMeasure Real) (x : Real) : Real :=
  ((mu : Measure Real) (Iic x)).toReal -
    ((nu : Measure Real) (Iic x)).toReal

/-- The left limit of the cumulative function of `mu - nu`. -/
def signedCumulativeLeft
    (mu nu : FiniteMeasure Real) (x : Real) : Real :=
  ((mu : Measure Real) (Iio x)).toReal -
    ((nu : Measure Real) (Iio x)).toReal

/-- The graph of the signed cumulative function, completed by a vertical
segment at every jump. -/
def generalizedCumulativeGraph
    (mu nu : FiniteMeasure Real) : Set (Real × Real) :=
  {p |
    p.2 ∈
      uIcc (signedCumulativeLeft mu nu p.1)
        (signedCumulative mu nu p.1)}

/-- A point of the completed cumulative graph at which the graph crosses its
level locally and strictly in the increasing direction. -/
def IsGoodIncreasingCrossing
    (mu nu : FiniteMeasure Real) (x h : Real) : Prop :=
  (x, h) ∈ generalizedCumulativeGraph mu nu /\
    ∃ epsilon > 0,
      ∀ ⦃x' h' : Real⦄,
        x' ∈ Ioo (x - epsilon) (x + epsilon) ->
          x' ≠ x ->
            (x', h') ∈ generalizedCumulativeGraph mu nu ->
              0 < (h' - h) * (x' - x)

/-- A point of the completed cumulative graph at which the graph crosses its
level locally and strictly in the decreasing direction. -/
def IsGoodDecreasingCrossing
    (mu nu : FiniteMeasure Real) (x h : Real) : Prop :=
  (x, h) ∈ generalizedCumulativeGraph mu nu /\
    ∃ epsilon > 0,
      ∀ ⦃x' h' : Real⦄,
        x' ∈ Ioo (x - epsilon) (x + epsilon) ->
          x' ≠ x ->
            (x', h') ∈ generalizedCumulativeGraph mu nu ->
              (h' - h) * (x' - x) < 0

/-- Two abscissae are consecutive intersections of the completed cumulative
graph with a fixed level. -/
def AreConsecutiveAtLevel
    (mu nu : FiniteMeasure Real) (h x y : Real) : Prop :=
  x < y /\
    (x, h) ∈ generalizedCumulativeGraph mu nu /\
      (y, h) ∈ generalizedCumulativeGraph mu nu /\
        ∀ z ∈ Ioo x y, (z, h) ∉ generalizedCumulativeGraph mu nu

/-- A relaxed local canonical-route over-approximation: consecutive locally
strict increasing/decreasing crossings of a common positive level. This does
not encode global regular-level finiteness or alternation. -/
def juilletCanonicalRouteSet
    (mu nu : FiniteMeasure Real) : Set (Real × Real) :=
  {p |
    ∃ h : Real,
      0 < h /\
        IsGoodIncreasingCrossing mu nu p.1 h /\
          IsGoodDecreasingCrossing mu nu p.2 h /\
            AreConsecutiveAtLevel mu nu h p.1 p.2}

end ConcaveOTLimit

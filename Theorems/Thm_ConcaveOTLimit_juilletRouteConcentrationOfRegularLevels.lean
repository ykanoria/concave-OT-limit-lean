import Theorems.Thm_ConcaveOTLimit_finiteCouplingMarginalAeTransfer
import Theorems.Thm_ConcaveOTLimit_existsStrictMonotoneArchSupportOfJuilletExcursionPlan
import Theorems.Thm_ConcaveOTLimit_monotoneArchMemCanonicalRouteOfRegularLevel

open MeasureTheory Set

namespace ConcaveOTLimit

/-- Source-a.e. positive regular cumulative levels concentrate a Juillet
excursion coupling on `juilletCanonicalRouteSet`. The conclusion concerns only
the declared relaxed local route set; it does not construct Juillet's global
finite alternating level pairing. -/
theorem juilletRouteConcentrationOfRegularLevels
    {mu nu : FiniteMeasure Real}
    {gamma : FiniteCoupling mu nu}
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (hExcursion : IsJuilletExcursionPlan mu nu gamma.plan)
    (hRegularLevels :
      ∀ᵐ x ∂(mu : Measure Real),
        0 < signedCumulative mu nu x ∧
          ∀ z : Real,
            (z, signedCumulative mu nu x) ∈
                generalizedCumulativeGraph mu nu ->
              IsGoodIncreasingCrossing
                  mu nu z (signedCumulative mu nu x) ∨
                IsGoodDecreasingCrossing
                  mu nu z (signedCumulative mu nu x)) :
    IsSupported gamma (juilletCanonicalRouteSet mu nu) := by
  obtain ⟨S, _hSMeasurable, hFull, hStrict, hMonotone⟩ :=
    existsStrictMonotoneArchSupportOfJuilletExcursionPlan
      hSingular hAtomless hOrder hExcursion
  have hForward : IsForwardPlan gamma := by
    filter_upwards [hFull] with z hzS
    rcases z with ⟨x, y⟩
    exact (hStrict hzS).le
  have hTargetTrue :
      ∀ᵐ _y ∂(nu : Measure Real), True := by
    simp
  have hRegularPlan :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)),
        0 < signedCumulative mu nu z.1 ∧
          ∀ r : Real,
            (r, signedCumulative mu nu z.1) ∈
                generalizedCumulativeGraph mu nu ->
              IsGoodIncreasingCrossing
                  mu nu r (signedCumulative mu nu z.1) ∨
                IsGoodDecreasingCrossing
                  mu nu r (signedCumulative mu nu z.1) :=
    (finiteCouplingMarginalAeTransfer
      gamma hRegularLevels hTargetTrue).1
  change
    ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)),
      z ∈ juilletCanonicalRouteSet mu nu
  filter_upwards [hFull, hRegularPlan] with z hzS hzRegular
  rcases z with ⟨x, y⟩
  refine
    monotoneArchMemCanonicalRouteOfRegularLevel
      gamma hAtomless hForward S hFull hMonotone hzS
        (hStrict hzS) hzRegular.1 ?_
  intro r _hr hGraph
  exact hzRegular.2 r hGraph

end ConcaveOTLimit

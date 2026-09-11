import Theorems.Thm_ConcaveOTLimit_existsJuilletExcursionMapCoupling
import Theorems.Thm_ConcaveOTLimit_literalJuilletMeasure
import Theorems.Thm_ConcaveOTLimit_literalJuilletPairingConstruction
import Theorems.Thm_ConcaveOTLimit_positiveCrossingIndicatrixAtomless

open MeasureTheory

namespace ConcaveOTLimit

/-- A map explicitly realizes the literal completed-graph Juillet coupling
when it induces the coupling, the coupling is exactly a literal Juillet
occupation measure, and its graph follows the canonical routes source-almost
everywhere. -/
def IsCanonicalJuilletExcursionMap
    (mu nu : FiniteMeasure Real)
    (gamma : FiniteCoupling mu nu)
    (T : Real -> Real) : Prop :=
  IsGraphPlan gamma T /\
    IsLiteralJuilletExcursionPlan mu nu gamma.plan /\
      ∀ᵐ x ∂(mu : Measure Real),
        (x, T x) ∈ juilletCanonicalRouteSet mu nu

/-- Under the hypotheses of paper Theorem 5, the unique old-style Juillet
coupling has an explicitly characterized literal completed-graph map. -/
theorem existsCanonicalJuilletExcursionMap
    (mu nu : FiniteMeasure Real)
    (hMass : mu.mass = nu.mass)
    (hPositive : 0 < mu.mass)
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu) :
    ∃ (gammaEC : FiniteCoupling mu nu) (T : Real -> Real),
      IsCanonicalJuilletExcursionMap mu nu gammaEC T /\
        IsForwardPlan gammaEC /\
        IsJuilletExcursionPlan mu nu gammaEC.plan /\
        (∀ gamma : FiniteCoupling mu nu,
          IsJuilletExcursionPlan mu nu gamma.plan ->
            gamma = gammaEC) /\
        ∀ S, IsGraphPlan gammaEC S ->
          S =ᵐ[(mu : Measure Real)] T := by
  obtain
      ⟨gammaEC, T, hGraph, hForward, hExcursion,
        hCouplingUnique, hMapUnique⟩ :=
    existsJuilletExcursionMapCoupling
      mu nu hMass hPositive hFirstMu hFirstNu
        hSingular hAtomless hOrder
  have hIndicatrix :
      PositiveCrossingIndicatrixIdentity mu nu :=
    positiveCrossingIndicatrixIdentity_of_atomless_mutuallySingular
      hAtomless hSingular
  obtain ⟨data, _hSource, _hTarget, hPlanLiteral⟩ :=
    literalJuilletPairingConstruction_of_juilletExcursionPlan
      mu nu gammaEC hExcursion hSingular hAtomless hOrder
        (measurablePositiveCrossingDecomposition mu nu) hIndicatrix
  have hLiteral :
      IsLiteralJuilletExcursionPlan mu nu gammaEC.plan :=
    ⟨gammaEC.property, data, hPlanLiteral⟩
  have hRouteSupport :
      IsSupported gammaEC (juilletCanonicalRouteSet mu nu) := by
    change
      ∀ᵐ z ∂(gammaEC.plan : Measure (Real × Real)),
        z ∈ juilletCanonicalRouteSet mu nu
    rw [hPlanLiteral]
    exact literalJuilletExcursionMeasure_supportedOnCanonicalRouteSet data
  have hRouteGraph :
      ∀ᵐ x ∂(mu : Measure Real),
        (x, T x) ∈ juilletCanonicalRouteSet mu nu :=
    canonicalRouteGraphSourceAe gammaEC hGraph hRouteSupport
  exact
    ⟨gammaEC, T, ⟨hGraph, hLiteral, hRouteGraph⟩,
      hForward, hExcursion, hCouplingUnique, hMapUnique⟩

/-- The selected representative of the canonical literal Juillet excursion
coupling. -/
noncomputable def canonicalJuilletExcursionCoupling
    (mu nu : FiniteMeasure Real)
    (hMass : mu.mass = nu.mass)
    (hPositive : 0 < mu.mass)
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu) :
    FiniteCoupling mu nu :=
  Classical.choose
    (existsCanonicalJuilletExcursionMap
      mu nu hMass hPositive hFirstMu hFirstNu
        hSingular hAtomless hOrder)

/-- A selected total representative of the canonical Juillet transport map.
Its source-almost-everywhere class is canonical. -/
noncomputable def canonicalJuilletExcursionMap
    (mu nu : FiniteMeasure Real)
    (hMass : mu.mass = nu.mass)
    (hPositive : 0 < mu.mass)
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu) :
    Real -> Real :=
  Classical.choose
    (Classical.choose_spec
      (existsCanonicalJuilletExcursionMap
        mu nu hMass hPositive hFirstMu hFirstNu
          hSingular hAtomless hOrder))

/-- The chosen coupling and map retain the full literal completed-graph,
canonical-route, forwardness, old Juillet, and uniqueness conclusions. -/
theorem canonicalJuilletExcursionMap_spec
    (mu nu : FiniteMeasure Real)
    (hMass : mu.mass = nu.mass)
    (hPositive : 0 < mu.mass)
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu) :
    IsCanonicalJuilletExcursionMap mu nu
        (canonicalJuilletExcursionCoupling
          mu nu hMass hPositive hFirstMu hFirstNu
            hSingular hAtomless hOrder)
        (canonicalJuilletExcursionMap
          mu nu hMass hPositive hFirstMu hFirstNu
            hSingular hAtomless hOrder) /\
      IsForwardPlan
        (canonicalJuilletExcursionCoupling
          mu nu hMass hPositive hFirstMu hFirstNu
            hSingular hAtomless hOrder) /\
      IsJuilletExcursionPlan mu nu
        (canonicalJuilletExcursionCoupling
          mu nu hMass hPositive hFirstMu hFirstNu
            hSingular hAtomless hOrder).plan /\
      (∀ gamma : FiniteCoupling mu nu,
        IsJuilletExcursionPlan mu nu gamma.plan ->
          gamma =
            canonicalJuilletExcursionCoupling
              mu nu hMass hPositive hFirstMu hFirstNu
                hSingular hAtomless hOrder) /\
      ∀ S,
        IsGraphPlan
            (canonicalJuilletExcursionCoupling
              mu nu hMass hPositive hFirstMu hFirstNu
                hSingular hAtomless hOrder) S ->
          S =ᵐ[(mu : Measure Real)]
            canonicalJuilletExcursionMap
              mu nu hMass hPositive hFirstMu hFirstNu
                hSingular hAtomless hOrder := by
  simpa only [canonicalJuilletExcursionCoupling,
    canonicalJuilletExcursionMap] using
    Classical.choose_spec
      (Classical.choose_spec
        (existsCanonicalJuilletExcursionMap
          mu nu hMass hPositive hFirstMu hFirstNu
            hSingular hAtomless hOrder))

/-- Every map inducing the canonical coupling agrees source-almost
everywhere with the selected canonical Juillet map. -/
theorem canonicalJuilletExcursionMap_ae_unique
    (mu nu : FiniteMeasure Real)
    (hMass : mu.mass = nu.mass)
    (hPositive : 0 < mu.mass)
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (S : Real -> Real)
    (hS :
      IsGraphPlan
        (canonicalJuilletExcursionCoupling
          mu nu hMass hPositive hFirstMu hFirstNu
            hSingular hAtomless hOrder) S) :
    S =ᵐ[(mu : Measure Real)]
      canonicalJuilletExcursionMap
        mu nu hMass hPositive hFirstMu hFirstNu
          hSingular hAtomless hOrder :=
  (canonicalJuilletExcursionMap_spec
    mu nu hMass hPositive hFirstMu hFirstNu
      hSingular hAtomless hOrder).2.2.2.2 S hS

#print axioms IsCanonicalJuilletExcursionMap
#print axioms existsCanonicalJuilletExcursionMap
#print axioms canonicalJuilletExcursionCoupling
#print axioms canonicalJuilletExcursionMap
#print axioms canonicalJuilletExcursionMap_spec
#print axioms canonicalJuilletExcursionMap_ae_unique

end ConcaveOTLimit

import Definitions.Def_excursion_coupling
import Mathlib.MeasureTheory.Measure.WithDensity

namespace ExcursionCoupling

open MeasureTheory Set Function

/-- The total number of increasing and decreasing completed-graph crossings
at a level, viewed as an extended nonnegative real number. -/
noncomputable def crossingMultiplicity (F : Real -> Real) (h : Real) : ENNReal :=
  ({x | (x, h) ∈ posPoints F}.encard.toENNReal) +
    ({x | (x, h) ∈ negPoints F}.encard.toENNReal)

/-- Juillet's law `theta / 2` for the randomly sampled completed-graph level. -/
noncomputable def excursionLevelLaw
    (mu nu : Measure Real) : Measure Real :=
  (2 : ENNReal)⁻¹ •
    (volume.withDensity (crossingMultiplicity (Fsigma mu nu)))

/-- The increasing crossing and its adjacent decreasing crossing at one
nonzero regular level, with the orientation prescribed by the sign. -/
def pairedAtLevel
    (F : Real -> Real) (h : Real) : Set (Real × Real) :=
  {r |
    h ≠ 0 ∧ regularLevel F h ∧
      (r.1, h) ∈ posPoints F ∧ (r.2, h) ∈ negPoints F ∧
        ((0 < h ∧ r.1 < r.2 ∧
            ∀ z ∈ Ioo r.1 r.2, z ∉ levelSet F h) ∨
          (h < 0 ∧ r.2 < r.1 ∧
            ∀ z ∈ Ioo r.2 r.1, z ∉ levelSet F h))}

/-- Measurable branch data for Juillet's completed-graph construction.
At almost every nonzero level, the active indices enumerate every increasing
and every decreasing crossing exactly once and pair adjacent crossings. -/
structure JuilletPairingData (mu nu : Measure Real) where
  source : Nat -> Real -> Real
  target : Nat -> Real -> Real
  active : Nat -> Set Real
  source_measurable : ∀ i, Measurable (source i)
  target_measurable : ∀ i, Measurable (target i)
  active_measurable : ∀ i, MeasurableSet (active i)
  active_nonzero : ∀ i, active i ⊆ {0}ᶜ
  regular_levels :
    ∀ᵐ h ∂(volume : Measure Real),
      h ≠ 0 -> regularLevel (Fsigma mu nu) h
  paired_ae :
    ∀ᵐ h ∂(volume : Measure Real),
      ∀ i, h ∈ active i ->
        (source i h, target i h) ∈ pairedAtLevel (Fsigma mu nu) h
  sources_exhaustive_unique_ae :
    ∀ᵐ h ∂(volume : Measure Real),
      ∀ x, h ≠ 0 -> regularLevel (Fsigma mu nu) h ->
        (x, h) ∈ posPoints (Fsigma mu nu) ->
          ∃! i : Nat, h ∈ active i ∧ source i h = x
  targets_exhaustive_unique_ae :
    ∀ᵐ h ∂(volume : Measure Real),
      ∀ y, h ≠ 0 -> regularLevel (Fsigma mu nu) h ->
        (y, h) ∈ negPoints (Fsigma mu nu) ->
          ∃! i : Nat, h ∈ active i ∧ target i h = y
  finite_active_ae :
    ∀ᵐ h ∂(volume : Measure Real), {i | h ∈ active i}.Finite

/-- The joint law obtained by integrating one atom at every adjacent
increasing/decreasing crossing pair over the completed-graph levels. This is
equivalent to sampling `H` with law `theta / 2` and then choosing uniformly
among the pairs at level `H`. -/
noncomputable def excursionCouplingMeasure
    {mu nu : Measure Real} (data : JuilletPairingData mu nu) :
    Measure (Real × Real) :=
  Measure.sum fun i =>
    Measure.map (fun h => (data.source i h, data.target i h))
      ((volume : Measure Real).restrict (data.active i))

/-- A measure is Juillet's excursion coupling when it has the prescribed
marginals and is exactly the completed-graph occupation measure. -/
def IsJuilletExcursionCoupling
    (mu nu : Measure Real) (gamma : Measure (Real × Real)) : Prop :=
  IsProbabilityMeasure gamma ∧
    gamma.map Prod.fst = mu ∧
      gamma.map Prod.snd = nu ∧
        ∃ data : JuilletPairingData mu nu,
          gamma = excursionCouplingMeasure data

end ExcursionCoupling

import Theorems.Thm_ConcaveOTLimit_juilletCumulativeLevelMapACOfPositiveCrossingMeasure
import Theorems.Thm_ConcaveOTLimit_juilletPositiveVariationMeasureEqSource
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory Set

namespace ConcaveOTLimit

/-- The measure obtained by integrating an enumerated family of crossing
points against Lebesgue measure on the level coordinate. -/
noncomputable def enumeratedPositiveCrossingMeasure
    (crossing : Nat -> Real -> Real) (levelSet : Nat -> Set Real) :
    Measure (Real × Real) :=
  Measure.sum fun n =>
    Measure.map (fun h => (crossing n h, h))
      ((volume : Measure Real).restrict (levelSet n))

private theorem measurableEmbedding_crossingPair
    {f : Real -> Real} (hf : Measurable f) :
    MeasurableEmbedding fun h : Real => (f h, h) := by
  refine
    { injective := ?_
      measurable := hf.prodMk measurable_id
      measurableSet_image' := ?_ }
  · intro a b hab
    exact congrArg Prod.snd hab
  · intro s hs
    have hImage :
        (fun h : Real => (f h, h)) '' s =
          {p : Real × Real | p.2 ∈ s ∧ p.1 = f p.2} := by
      ext p
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact ⟨hh, rfl⟩
      · rintro ⟨hp, heq⟩
        exact ⟨p.2, hp, Prod.ext heq.symm rfl⟩
    rw [hImage]
    exact
      (hs.preimage measurable_snd).inter
        (measurableSet_eq_fun measurable_fst (hf.comp measurable_snd))

/-- A measurable enumeration of good increasing crossings, together with its
positive occupation identity, constructs the crossing measure required by
`juilletCumulativeLevelMapACOfPositiveCrossingMeasure`. -/
theorem positiveCrossingMeasureConstruction
    {mu nu : FiniteMeasure Real}
    (hSingular : FiniteMutuallySingular mu nu)
    (crossing : Nat -> Real -> Real)
    (levelSet : Nat -> Set Real)
    (hCrossingMeasurable : ∀ n, Measurable (crossing n))
    (hOccupation :
      Measure.sum (fun n =>
          Measure.map (crossing n)
            ((volume : Measure Real).restrict (levelSet n))) =
        juilletPositiveVariationMeasure mu nu)
    (hCrossing :
      ∀ n,
        ∀ᵐ h ∂((volume : Measure Real).restrict (levelSet n)),
          IsGoodIncreasingCrossing mu nu (crossing n h) h) :
    ∃ zeta : Measure (Real × Real),
      Measure.map Prod.fst zeta = (mu : Measure Real) ∧
        Measure.map Prod.snd zeta ≪ (volume : Measure Real) ∧
          ∀ᵐ p ∂zeta,
            IsGoodIncreasingCrossing mu nu p.1 p.2 := by
  let zeta :=
    enumeratedPositiveCrossingMeasure crossing levelSet
  have hPairMeasurable (n : Nat) :
      Measurable fun h : Real => (crossing n h, h) :=
    (hCrossingMeasurable n).prodMk measurable_id
  have hFirstVariation :
      Measure.map Prod.fst zeta =
        juilletPositiveVariationMeasure mu nu := by
    dsimp [zeta]
    rw [enumeratedPositiveCrossingMeasure,
      Measure.map_sum measurable_fst.aemeasurable]
    calc
      Measure.sum (fun n =>
          Measure.map Prod.fst
            (Measure.map (fun h => (crossing n h, h))
              ((volume : Measure Real).restrict (levelSet n)))) =
          Measure.sum (fun n =>
            Measure.map (crossing n)
              ((volume : Measure Real).restrict (levelSet n))) := by
        apply Measure.sum_congr
        intro n
        rw [Measure.map_map measurable_fst (hPairMeasurable n)]
        rfl
      _ = juilletPositiveVariationMeasure mu nu := hOccupation
  have hFirst :
      Measure.map Prod.fst zeta = (mu : Measure Real) :=
    hFirstVariation.trans
      (juilletPositiveVariationMeasureEqSource hSingular)
  have hSecond :
      Measure.map Prod.snd zeta ≪ (volume : Measure Real) := by
    dsimp [zeta]
    rw [enumeratedPositiveCrossingMeasure,
      Measure.map_sum measurable_snd.aemeasurable]
    apply Measure.absolutelyContinuous_sum_left
    intro n
    rw [Measure.map_map measurable_snd (hPairMeasurable n)]
    simpa only [Function.comp_def, Measure.map_id'] using
      (Measure.absolutelyContinuous_restrict :
        (volume : Measure Real).restrict (levelSet n) ≪
          (volume : Measure Real))
  have hSupported :
      ∀ᵐ p ∂zeta,
        IsGoodIncreasingCrossing mu nu p.1 p.2 := by
    dsimp [zeta]
    rw [enumeratedPositiveCrossingMeasure,
      Measure.ae_sum_iff]
    intro n
    apply
      (measurableEmbedding_crossingPair
        (hCrossingMeasurable n)).ae_map_iff.mpr
    simpa only using hCrossing n
  exact ⟨zeta, hFirst, hSecond, hSupported⟩

/-- The positive occupation identity for measurable increasing-crossing
branches discharges the cumulative-level absolute-continuity premise used by
C154. -/
theorem juilletCumulativeLevelMapACOfPositiveCrossingEnumeration
    {mu nu : FiniteMeasure Real}
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (crossing : Nat -> Real -> Real)
    (levelSet : Nat -> Set Real)
    (hCrossingMeasurable : ∀ n, Measurable (crossing n))
    (hOccupation :
      Measure.sum (fun n =>
          Measure.map (crossing n)
            ((volume : Measure Real).restrict (levelSet n))) =
        juilletPositiveVariationMeasure mu nu)
    (hCrossing :
      ∀ n,
        ∀ᵐ h ∂((volume : Measure Real).restrict (levelSet n)),
          IsGoodIncreasingCrossing mu nu (crossing n h) h) :
    Measure.map (signedCumulative mu nu) (mu : Measure Real) ≪
      (volume : Measure Real) := by
  obtain ⟨zeta, hFirst, hSecond, hSupported⟩ :=
    positiveCrossingMeasureConstruction hSingular crossing levelSet
      hCrossingMeasurable hOccupation hCrossing
  exact
    juilletCumulativeLevelMapACOfPositiveCrossingMeasure
      mu nu hAtomless zeta hFirst hSecond hSupported

end ConcaveOTLimit

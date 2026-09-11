import Definitions.Def_ConcaveOTLimitModel

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    {mu nu : FiniteMeasure Real}
    {gamma : FiniteCoupling mu nu}
    {profile : Real -> Real}
    {support : Set (Real × Real)}
    (hSingular : FiniteMutuallySingular mu nu)
    (hForward : IsForwardPlan gamma)
    (hFull : IsSupported gamma support)
    (hLex :
      forall {x y x' y' : Real},
        (x, y) ∈ support -> (x', y') ∈ support ->
          dist x y + dist x' y' <= dist x y' + dist x' y /\
          (dist x y + dist x' y' = dist x y' + dist x' y ->
            profile (dist x y) + profile (dist x' y') <=
              profile (dist x y') + profile (dist x' y))) :
    exists strictSupport : Set (Real × Real),
      IsSupported gamma strictSupport /\
      (forall {x y : Real}, (x, y) ∈ strictSupport -> x < y) /\
      (forall {x y x' y' : Real},
        (x, y) ∈ strictSupport -> (x', y') ∈ strictSupport ->
          dist x y + dist x' y' <= dist x y' + dist x' y /\
          (dist x y + dist x' y' = dist x y' + dist x' y ->
            profile (dist x y) + profile (dist x' y') <=
              profile (dist x y') + profile (dist x' y))) := by
  obtain ⟨s, hs, hMu, hNu⟩ := hSingular
  have hFirstMarginal : firstMarginal gamma.plan = mu := by
    simpa [FiniteCoupling.plan] using gamma.property.1
  have hSecondMarginal : secondMarginal gamma.plan = nu := by
    simpa [FiniteCoupling.plan] using gamma.property.2
  have hSourceMap :
      ∀ᵐ x ∂Measure.map Prod.fst
        (gamma.plan : Measure (Real × Real)), x ∈ s := by
    change ∀ᵐ x ∂(firstMarginal gamma.plan : Measure Real), x ∈ s
    rw [hFirstMarginal]
    apply ae_iff.mpr
    change (mu : Measure Real) sᶜ = 0
    exact hMu
  have hTargetMap :
      ∀ᵐ y ∂Measure.map Prod.snd
        (gamma.plan : Measure (Real × Real)), y ∉ s := by
    change ∀ᵐ y ∂(secondMarginal gamma.plan : Measure Real), y ∉ s
    rw [hSecondMarginal]
    apply ae_iff.mpr
    have hSet : {a : Real | ¬a ∉ s} = s := by
      ext a
      simp only [mem_setOf_eq, not_not]
    rw [hSet]
    exact hNu
  have hSource :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.1 ∈ s :=
    (ae_map_iff measurable_fst.aemeasurable hs).mp hSourceMap
  have hTarget :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.2 ∉ s :=
    (ae_map_iff measurable_snd.aemeasurable hs.compl).mp hTargetMap
  have hNe :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.1 ≠ z.2 := by
    filter_upwards [hSource, hTarget] with z hzSource hzTarget
    intro heq
    exact hzTarget (heq ▸ hzSource)
  let strictSupport := support ∩ {z : Real × Real | z.1 < z.2}
  refine ⟨strictSupport, ?_, ?_, ?_⟩
  · filter_upwards [hFull, hForward, hNe] with z hz hle hne
    exact ⟨hz, lt_of_le_of_ne hle hne⟩
  · intro x y hxy
    exact hxy.2
  · intro x y x' y' hxy hxy'
    exact hLex hxy.1 hxy'.1

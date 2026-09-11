import Definitions.Def_ConcaveOTLimitModel

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    {mu nu : FiniteMeasure E} (gamma : FiniteCoupling mu nu) :
    IsDistanceOptimal gamma <->
      distanceCost gamma = minimalDistanceCost mu nu := by
  have hDistanceNonnegative :
      ∀ eta : FiniteCoupling mu nu, 0 <= distanceCost eta := by
    intro eta
    unfold distanceCost profileCost
    exact integral_nonneg fun z => norm_nonneg (z.1 - z.2)
  have hRangeBounded :
      BddBelow
        (Set.range
          (distanceCost : FiniteCoupling mu nu -> Real)) := by
    refine ⟨0, ?_⟩
    rintro value ⟨eta, rfl⟩
    exact hDistanceNonnegative eta
  constructor
  · rintro ⟨-, hMinimal⟩
    unfold minimalDistanceCost
    have hLeast :
        IsLeast
          (Set.range
            (distanceCost : FiniteCoupling mu nu -> Real))
          (distanceCost gamma) := by
      refine ⟨⟨gamma, rfl⟩, ?_⟩
      rintro value ⟨eta, rfl⟩
      exact hMinimal eta (mem_univ eta)
    exact hLeast.csInf_eq.symm
  · intro hAttains
    refine ⟨mem_univ gamma, ?_⟩
    intro eta _heta
    change distanceCost gamma <= distanceCost eta
    rw [hAttains]
    unfold minimalDistanceCost
    exact csInf_le hRangeBounded ⟨eta, rfl⟩

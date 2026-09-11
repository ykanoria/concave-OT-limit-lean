import Definitions.Def_ConcaveOTLimitModel
import Theorems.Thm_ConcaveOTLimit_existsStrictForwardLexicographicSupport
import Theorems.Thm_ConcaveOTLimit_existsFullMassMonotoneArchSupport
import Mathlib.Tactic.Linarith

open MeasureTheory Set

namespace ConcaveOTLimit

private theorem orderedArchesDoNotCross
    {x y x' y' : Real}
    (hxy : x < y) (hxy' : x' < y')
    (hNoCross :
      Not ((x < x' /\ x' < y /\ y < y') \/
        (x' < x /\ x < y' /\ y' < y))) :
    ArchesDoNotCross (x, y) (x', y') := by
  change
    Disjoint (uIcc x y) (uIcc x' y') \/
      (exists z, uIcc x y ∩ uIcc x' y' = {z}) \/
      uIcc x y ⊆ uIcc x' y' \/
      uIcc x' y' ⊆ uIcc x y
  rcases lt_trichotomy x x' with hxx' | hxx' | hxx'
  · rcases lt_trichotomy y x' with hyx' | hyx' | hyx'
    · left
      rw [uIcc_of_le hxy.le, uIcc_of_le hxy'.le]
      refine Set.disjoint_left.2 ?_
      intro z hz hz'
      simp only [mem_Icc] at hz hz'
      linarith
    · right
      left
      refine ⟨y, ?_⟩
      rw [uIcc_of_le hxy.le, uIcc_of_le hxy'.le]
      ext z
      simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
      constructor
      · rintro ⟨hz, hz'⟩
        linarith
      · intro hz
        subst z
        constructor <;> constructor <;> linarith
    · right
      right
      right
      have hy'y : y' <= y := by
        by_contra h
        exact hNoCross (Or.inl ⟨hxx', hyx', lt_of_not_ge h⟩)
      rw [uIcc_of_le hxy'.le, uIcc_of_le hxy.le]
      intro z hz
      exact ⟨hxx'.le.trans hz.1, hz.2.trans hy'y⟩
  · subst x'
    rcases le_total y y' with hyy' | hy'y
    · right
      right
      left
      rw [uIcc_of_le hxy.le, uIcc_of_le hxy'.le]
      intro z hz
      exact ⟨hz.1, hz.2.trans hyy'⟩
    · right
      right
      right
      rw [uIcc_of_le hxy'.le, uIcc_of_le hxy.le]
      intro z hz
      exact ⟨hz.1, hz.2.trans hy'y⟩
  · rcases lt_trichotomy y' x with hy'x | hy'x | hy'x
    · left
      rw [uIcc_of_le hxy.le, uIcc_of_le hxy'.le]
      refine Set.disjoint_left.2 ?_
      intro z hz hz'
      simp only [mem_Icc] at hz hz'
      linarith
    · right
      left
      refine ⟨x, ?_⟩
      rw [uIcc_of_le hxy.le, uIcc_of_le hxy'.le]
      ext z
      simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
      constructor
      · rintro ⟨hz, hz'⟩
        linarith
      · intro hz
        subst z
        constructor <;> constructor <;> linarith
    · right
      right
      left
      have hyy' : y <= y' := by
        by_contra h
        exact hNoCross (Or.inr ⟨hxx', hy'x, lt_of_not_ge h⟩)
      rw [uIcc_of_le hxy'.le, uIcc_of_le hxy.le]
      intro z hz
      exact ⟨hxx'.le.trans hz.1, hz.2.trans hyy'⟩

private theorem orderedArchesDoNotConnect
    {x y x' y' : Real}
    (hNoConnect : y ≠ x' /\ y' ≠ x) :
    ArchesDoNotConnect (x, y) (x', y') := by
  intro _
  exact hNoConnect.1

private theorem orderedNestedArchesHaveSameOrientation
    {x y x' y' : Real}
    (hxy : x < y)
    (hOrientation :
      ((x < x' /\ y' < y) \/ (x' < x /\ y < y')) ->
        0 <= (y - x) * (y' - x')) :
    NestedArchesHaveSameOrientation (x, y) (x', y') := by
  intro hNested
  apply hOrientation
  left
  have hx' := hNested (left_mem_uIcc : x' ∈ uIcc x' y')
  have hy' := hNested (right_mem_uIcc : y' ∈ uIcc x' y')
  rw [uIoo_of_le hxy.le] at hx' hy'
  exact ⟨hx'.1, hy'.2⟩

/-- A measurable full-mass forward lexicographic support can be refined,
without losing measurability, to a full-mass monotone-arch support. -/
theorem existsMeasurableFullMassMonotoneArchSupport
    {mu nu : FiniteMeasure Real}
    {gamma : FiniteCoupling mu nu}
    {profile : Real -> Real}
    {support : Set (Real × Real)}
    (hProfile : StrictConcaveOn Real (Ici 0) profile)
    (hSingular : FiniteMutuallySingular mu nu)
    (hForward : IsForwardPlan gamma)
    (hMeasurable : MeasurableSet support)
    (hFull : IsSupported gamma support)
    (hLex :
      forall {x y x' y' : Real},
        (x, y) ∈ support -> (x', y') ∈ support ->
          dist x y + dist x' y' <= dist x y' + dist x' y /\
          (dist x y + dist x' y' = dist x y' + dist x' y ->
            profile (dist x y) + profile (dist x' y') <=
              profile (dist x y') + profile (dist x' y))) :
    exists monotoneSupport : Set (Real × Real),
      MeasurableSet monotoneSupport /\
      IsSupported gamma monotoneSupport /\
      IsMonotoneArchSet monotoneSupport := by
  obtain
      ⟨strictWitness, hWitnessFull, hWitnessForward, _hWitnessLex⟩ :=
    existsStrictForwardLexicographicSupport
      hSingular hForward hFull hLex
  have hStrictAE :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.1 < z.2 := by
    filter_upwards [hWitnessFull] with z hz
    exact hWitnessForward hz
  let monotoneSupport :=
    support ∩ {z : Real × Real | z.1 < z.2}
  have hMonotoneMeasurable : MeasurableSet monotoneSupport := by
    exact hMeasurable.inter
      (measurableSet_lt measurable_fst measurable_snd)
  have hMonotoneFull : IsSupported gamma monotoneSupport := by
    filter_upwards [hFull, hStrictAE] with z hz hlt
    exact ⟨hz, hlt⟩
  have hStrictForward :
      forall {x y : Real}, (x, y) ∈ monotoneSupport -> x < y := by
    intro x y hxy
    exact hxy.2
  have hStrictLex :
      forall {x y x' y' : Real},
        (x, y) ∈ monotoneSupport -> (x', y') ∈ monotoneSupport ->
          dist x y + dist x' y' <= dist x y' + dist x' y /\
          (dist x y + dist x' y' = dist x y' + dist x' y ->
            profile (dist x y) + profile (dist x' y') <=
              profile (dist x y') + profile (dist x' y)) := by
    intro x y x' y' hxy hxy'
    exact hLex hxy.1 hxy'.1
  have hOrdered :=
    strictForwardLexicographicSupportIsJuilletMonotone
      hProfile hStrictForward hStrictLex
  refine ⟨monotoneSupport, hMonotoneMeasurable, hMonotoneFull, ?_⟩
  intro p hp q hq
  rcases p with ⟨x, y⟩
  rcases q with ⟨x', y'⟩
  exact
    ⟨orderedArchesDoNotCross
        (hOrdered.1 hp) (hOrdered.1 hq)
        (hOrdered.2.1 hp hq),
      orderedArchesDoNotConnect (hOrdered.2.2.1 hp hq),
      orderedNestedArchesHaveSameOrientation
        (hOrdered.1 hp) (hOrdered.2.2.2 hp hq)⟩

end ConcaveOTLimit

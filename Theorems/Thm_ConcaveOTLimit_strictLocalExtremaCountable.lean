import Mathlib.Data.Rat.Encodable
import Mathlib.Topology.Instances.Real.Lemmas

open Set

namespace ConcaveOTLimit

private theorem strictLocalMaximaCountable
    (f : Real -> Real) :
    {x : Real |
      exists epsilon, 0 < epsilon ∧
        forall y : Real,
          y ∈ Ioo (x - epsilon) (x + epsilon) ->
            y ≠ x -> f y < f x}.Countable := by
  let s : Set Real :=
    {x : Real |
      exists epsilon, 0 < epsilon ∧
        forall y : Real,
          y ∈ Ioo (x - epsilon) (x + epsilon) ->
            y ≠ x -> f y < f x}
  let epsilon : s -> Real := fun x => Classical.choose x.property
  have hEpsilon :
      forall x : s,
        0 < epsilon x ∧
          forall y : Real,
            y ∈ Ioo (x.1 - epsilon x) (x.1 + epsilon x) ->
              y ≠ x.1 -> f y < f x.1 := by
    intro x
    exact Classical.choose_spec x.property
  let left : s -> Rat := fun x =>
    Classical.choose
      (exists_rat_btwn (sub_lt_self x.1 (hEpsilon x).1))
  have hLeft :
      forall x : s,
        x.1 - epsilon x < (left x : Real) ∧ (left x : Real) < x.1 := by
    intro x
    exact Classical.choose_spec
      (exists_rat_btwn (sub_lt_self x.1 (hEpsilon x).1))
  let right : s -> Rat := fun x =>
    Classical.choose
      (exists_rat_btwn (lt_add_of_pos_right x.1 (hEpsilon x).1))
  have hRight :
      forall x : s,
        x.1 < (right x : Real) ∧ (right x : Real) < x.1 + epsilon x := by
    intro x
    exact Classical.choose_spec
      (exists_rat_btwn (lt_add_of_pos_right x.1 (hEpsilon x).1))
  let code : s -> Rat × Rat := fun x => (left x, right x)
  have hCode : Function.Injective code := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hLeftEq : left x = left y := congrArg Prod.fst hxy
    have hRightEq : right x = right y := congrArg Prod.snd hxy
    have hyMem :
        y.1 ∈ Ioo (x.1 - epsilon x) (x.1 + epsilon x) := by
      constructor
      · exact (hLeft x).1.trans
          (by simpa only [hLeftEq] using (hLeft y).2)
      · have hyRight : y.1 < (right x : Real) := by
          simpa only [hRightEq] using (hRight y).1
        exact hyRight.trans (hRight x).2
    have hxMem :
        x.1 ∈ Ioo (y.1 - epsilon y) (y.1 + epsilon y) := by
      constructor
      · exact (hLeft y).1.trans
          (by simpa only [hLeftEq] using (hLeft x).2)
      · have hxRight : x.1 < (right y : Real) := by
          simpa only [hRightEq] using (hRight x).1
        exact hxRight.trans (hRight y).2
    have hyx : f y.1 < f x.1 :=
      (hEpsilon x).2 y.1 hyMem (Ne.symm hne)
    have hxy' : f x.1 < f y.1 :=
      (hEpsilon y).2 x.1 hxMem hne
    exact (not_lt_of_ge hyx.le) hxy'
  change s.Countable
  exact hCode.countable

/-- The points at which a real function has a strict local maximum or a
strict local minimum form a countable set. -/
theorem strictLocalExtremaCountable
    (f : Real -> Real) :
    {x : Real |
      (exists epsilon, 0 < epsilon ∧
        forall y : Real,
          y ∈ Ioo (x - epsilon) (x + epsilon) ->
            y ≠ x -> f y < f x) ∨
      (exists epsilon, 0 < epsilon ∧
        forall y : Real,
          y ∈ Ioo (x - epsilon) (x + epsilon) ->
            y ≠ x -> f x < f y)}.Countable := by
  let maxima : Set Real :=
    {x : Real |
      exists epsilon, 0 < epsilon ∧
        forall y : Real,
          y ∈ Ioo (x - epsilon) (x + epsilon) ->
            y ≠ x -> f y < f x}
  let minima : Set Real :=
    {x : Real |
      exists epsilon, 0 < epsilon ∧
        forall y : Real,
          y ∈ Ioo (x - epsilon) (x + epsilon) ->
            y ≠ x -> f x < f y}
  have hMaxima : maxima.Countable := by
    simpa only [maxima] using strictLocalMaximaCountable f
  have hMinima : minima.Countable := by
    have hNeg := strictLocalMaximaCountable (fun x => -f x)
    simpa only [minima, neg_lt_neg_iff] using hNeg
  simpa only [maxima, minima, mem_setOf_eq, union_def] using
    hMaxima.union hMinima

end ConcaveOTLimit

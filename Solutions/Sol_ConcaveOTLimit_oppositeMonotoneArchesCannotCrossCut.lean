import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Tactic.Linarith

open Set

open ConcaveOTLimit

theorem solution
    {x y x' y' t : Real}
    (hBackward : y <= t /\ t < x)
    (hForward : x' < t /\ t < y')
    (hNoCross : ArchesDoNotCross (x, y) (x', y'))
    (hNoConnect : ArchesDoNotConnect (x, y) (x', y'))
    (hNoConnectRev : ArchesDoNotConnect (x', y') (x, y))
    (hOrientation : NestedArchesHaveSameOrientation (x, y) (x', y'))
    (hOrientationRev :
      NestedArchesHaveSameOrientation (x', y') (x, y)) :
    False := by
  have hyx : y < x := hBackward.1.trans_lt hBackward.2
  have hx'y' : x' < y' := hForward.1.trans hForward.2
  have hLengths :
      0 < min |y - x| |y' - x'| := by
    apply lt_min
    · exact abs_pos.mpr (sub_ne_zero.mpr hyx.ne)
    · exact abs_pos.mpr (sub_ne_zero.mpr hx'y'.ne')
  have hNotYX' : y ≠ x' := hNoConnect hLengths
  have hNotY'X : y' ≠ x := hNoConnectRev (by simpa [min_comm] using hLengths)
  have htBackward : t ∈ uIcc x y :=
    mem_uIcc_of_ge hBackward.1 hBackward.2.le
  have htForward : t ∈ uIcc x' y' :=
    mem_uIcc_of_le hForward.1.le hForward.2.le
  have hMin : t < min x y' := lt_min hBackward.2 hForward.2
  let s : Real := (t + min x y') / 2
  have hts : t < s := by
    dsimp [s]
    linarith
  have hsMin : s < min x y' := by
    dsimp [s]
    linarith
  have hsBackward : s ∈ uIcc x y :=
    mem_uIcc_of_ge (hBackward.1.trans hts.le)
      (hsMin.trans_le (min_le_left _ _)).le
  have hsForward : s ∈ uIcc x' y' :=
    mem_uIcc_of_le (hForward.1.le.trans hts.le)
      (hsMin.trans_le (min_le_right _ _)).le
  rcases hNoCross with hDisjoint | hSingleton | hBackwardSubset | hForwardSubset
  · exact Set.disjoint_left.1 hDisjoint htBackward htForward
  · obtain ⟨z, hz⟩ := hSingleton
    have htEq : t = z := by
      have : t ∈ ({z} : Set Real) := by
        rw [← hz]
        exact ⟨htBackward, htForward⟩
      simpa using this
    have hsEq : s = z := by
      have : s ∈ ({z} : Set Real) := by
        rw [← hz]
        exact ⟨hsBackward, hsForward⟩
      simpa using this
    linarith
  · have hyMem : y ∈ uIcc x' y' :=
      hBackwardSubset right_mem_uIcc
    have hxMem : x ∈ uIcc x' y' :=
      hBackwardSubset left_mem_uIcc
    rw [uIcc_of_le hx'y'.le] at hyMem hxMem
    have hx'y : x' < y := lt_of_le_of_ne hyMem.1 (Ne.symm hNotYX')
    have hxy' : x < y' := lt_of_le_of_ne hxMem.2 (Ne.symm hNotY'X)
    have hStrictSubset : uIcc x y ⊆ uIoo x' y' := by
      intro z hz
      rw [uIcc_comm, uIcc_of_le hyx.le] at hz
      rw [uIoo_of_le hx'y'.le]
      exact ⟨hx'y.trans_le hz.1, hz.2.trans_lt hxy'⟩
    have hProduct := hOrientationRev hStrictSubset
    have hForwardDisplacement : 0 < y' - x' := sub_pos.mpr hx'y'
    have hBackwardDisplacement : y - x < 0 := sub_neg.mpr hyx
    nlinarith
  · have hx'Mem : x' ∈ uIcc x y :=
      hForwardSubset left_mem_uIcc
    have hy'Mem : y' ∈ uIcc x y :=
      hForwardSubset right_mem_uIcc
    rw [uIcc_comm, uIcc_of_le hyx.le] at hx'Mem hy'Mem
    have hyx' : y < x' := lt_of_le_of_ne hx'Mem.1 hNotYX'
    have hy'x : y' < x := lt_of_le_of_ne hy'Mem.2 hNotY'X
    have hStrictSubset : uIcc x' y' ⊆ uIoo x y := by
      intro z hz
      rw [uIcc_of_le hx'y'.le] at hz
      rw [uIoo_comm, uIoo_of_le hyx.le]
      exact ⟨hyx'.trans_le hz.1, hz.2.trans_lt hy'x⟩
    have hProduct := hOrientation hStrictSubset
    have hForwardDisplacement : 0 < y' - x' := sub_pos.mpr hx'y'
    have hBackwardDisplacement : y - x < 0 := sub_neg.mpr hyx
    nlinarith

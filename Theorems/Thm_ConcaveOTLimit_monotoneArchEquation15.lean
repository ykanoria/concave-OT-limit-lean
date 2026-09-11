import Definitions.Def_ConcaveOTLimitModel

open MeasureTheory Set

namespace ConcaveOTLimit

private theorem crossingRectanglePointImpossible
    {x y a b : Real}
    (hxy : x < y)
    (ha : a ∈ (Icc x y)ᶜ)
    (hb : b ∈ Ioo x y)
    (hbNeX : b ≠ x)
    (hbNeY : b ≠ y)
    (hNoCross : ArchesDoNotCross (x, y) (a, b)) :
    False := by
  have ha' : ¬(x ≤ a ∧ a ≤ y) := by
    simpa only [mem_compl_iff, mem_Icc] using ha
  rcases not_and_or.mp ha' with hax | hya
  · have hax' : a < x := lt_of_not_ge hax
    have hab : a < b := hax'.trans hb.1
    have hxLeft : x ∈ uIcc x y := left_mem_uIcc
    have hxRight : x ∈ uIcc a b :=
      mem_uIcc_of_le hax'.le hb.1.le
    have hbLeft : b ∈ uIcc x y :=
      mem_uIcc_of_le hb.1.le hb.2.le
    have hbRight : b ∈ uIcc a b := right_mem_uIcc
    rcases hNoCross with
      hDisjoint | hSingleton | hLeftSubset | hRightSubset
    · exact Set.disjoint_left.mp hDisjoint hxLeft hxRight
    · obtain ⟨z, hz⟩ := hSingleton
      have hxz : x = z := by
        have hxMem : x ∈ ({z} : Set Real) := by
          rw [← hz]
          exact ⟨hxLeft, hxRight⟩
        simpa only [mem_singleton_iff] using hxMem
      have hbz : b = z := by
        have hbMem : b ∈ ({z} : Set Real) := by
          rw [← hz]
          exact ⟨hbLeft, hbRight⟩
        simpa only [mem_singleton_iff] using hbMem
      exact hbNeX (hxz.trans hbz.symm).symm
    · have hyRight :=
        hLeftSubset (right_mem_uIcc : y ∈ uIcc x y)
      rw [uIcc_of_le hab.le] at hyRight
      exact (not_le_of_gt hb.2) hyRight.2
    · have haLeft :=
        hRightSubset (left_mem_uIcc : a ∈ uIcc a b)
      rw [uIcc_of_le hxy.le] at haLeft
      exact (not_le_of_gt hax') haLeft.1
  · have hya' : y < a := lt_of_not_ge hya
    have hba : b < a := hb.2.trans hya'
    have hbLeft : b ∈ uIcc x y :=
      mem_uIcc_of_le hb.1.le hb.2.le
    have hbRight : b ∈ uIcc a b := right_mem_uIcc
    have hyLeft : y ∈ uIcc x y := right_mem_uIcc
    have hyRight : y ∈ uIcc a b :=
      mem_uIcc_of_ge hb.2.le hya'.le
    rcases hNoCross with
      hDisjoint | hSingleton | hLeftSubset | hRightSubset
    · exact Set.disjoint_left.mp hDisjoint hbLeft hbRight
    · obtain ⟨z, hz⟩ := hSingleton
      have hbz : b = z := by
        have hbMem : b ∈ ({z} : Set Real) := by
          rw [← hz]
          exact ⟨hbLeft, hbRight⟩
        simpa only [mem_singleton_iff] using hbMem
      have hyz : y = z := by
        have hyMem : y ∈ ({z} : Set Real) := by
          rw [← hz]
          exact ⟨hyLeft, hyRight⟩
        simpa only [mem_singleton_iff] using hyMem
      exact hbNeY (hbz.trans hyz.symm)
    · have hxRight :=
        hLeftSubset (left_mem_uIcc : x ∈ uIcc x y)
      rw [uIcc_of_ge hba.le] at hxRight
      exact (not_le_of_gt hb.1) hxRight.1
    · have haLeft :=
        hRightSubset (left_mem_uIcc : a ∈ uIcc a b)
      rw [uIcc_of_le hxy.le] at haLeft
      exact (not_le_of_gt hya') haLeft.2

/-- Juillet's equation (15): no mass can have exactly one endpoint strictly
inside a forward arch while the other endpoint lies outside its closed span. -/
theorem monotoneArchEquation15
    (rho : FiniteMeasure (Real × Real))
    (S : Set (Real × Real))
    (hFull : ∀ᵐ z ∂(rho : Measure (Real × Real)), z ∈ S)
    (hMonotone : IsMonotoneArchSet S)
    {x y : Real}
    (hArch : (x, y) ∈ S)
    (hxy : x < y) :
    (rho : Measure (Real × Real)) ((Icc x y)ᶜ ×ˢ Ioo x y) = 0 ∧
      (rho : Measure (Real × Real)) (Ioo x y ×ˢ (Icc x y)ᶜ) = 0 := by
  constructor
  · have hAvoid :
        ∀ᵐ z ∂(rho : Measure (Real × Real)),
          z ∉ (Icc x y)ᶜ ×ˢ Ioo x y := by
      filter_upwards [hFull] with z hz
      intro hzRectangle
      have hConditions := hMonotone (x, y) hArch z hz
      have hConditionsRev := hMonotone z hz (x, y) hArch
      have hzNe : z.2 ≠ z.1 := by
        intro hEq
        apply hzRectangle.1
        rw [← hEq]
        exact Ioo_subset_Icc_self hzRectangle.2
      have hLengthsRev :
          0 < min |z.2 - z.1| |y - x| := by
        apply lt_min
        · exact abs_pos.mpr (sub_ne_zero.mpr hzNe)
        · exact abs_pos.mpr (sub_ne_zero.mpr hxy.ne')
      exact crossingRectanglePointImpossible hxy hzRectangle.1 hzRectangle.2
        (hConditionsRev.2.1 hLengthsRev) hzRectangle.2.2.ne
        hConditions.1
    simpa only [ae_iff, Classical.not_not, setOf_mem_eq] using hAvoid
  · have hAvoid :
        ∀ᵐ z ∂(rho : Measure (Real × Real)),
          z ∉ Ioo x y ×ˢ (Icc x y)ᶜ := by
      filter_upwards [hFull] with z hz
      intro hzRectangle
      have hConditions := hMonotone (x, y) hArch z hz
      have hzNe : z.2 ≠ z.1 := by
        intro hEq
        apply hzRectangle.2
        rw [hEq]
        exact Ioo_subset_Icc_self hzRectangle.1
      have hLengths :
          0 < min |y - x| |z.2 - z.1| := by
        apply lt_min
        · exact abs_pos.mpr (sub_ne_zero.mpr hxy.ne')
        · exact abs_pos.mpr (sub_ne_zero.mpr hzNe)
      have hInsideNeY : z.1 ≠ y :=
        (hConditions.2.1 hLengths).symm
      have hNoCross :
          ArchesDoNotCross (x, y) (z.2, z.1) := by
        simpa only [ArchesDoNotCross, uIcc_comm] using
          hConditions.1
      exact crossingRectanglePointImpossible hxy hzRectangle.2 hzRectangle.1
        hzRectangle.1.1.ne' hInsideNeY hNoCross
    simpa only [ae_iff, Classical.not_not, setOf_mem_eq] using hAvoid

end ConcaveOTLimit

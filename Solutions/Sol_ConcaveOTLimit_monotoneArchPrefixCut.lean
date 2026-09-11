import Theorems.Thm_ConcaveOTLimit_monotoneArchEquation15

open MeasureTheory Set

open ConcaveOTLimit

private theorem internalBackwardArchImpossible
    {x y a b t : Real}
    (ht : t ∈ Ioo x y)
    (ha : a ∈ Icc x y)
    (haPrefix : a ∈ (Icc x t)ᶜ)
    (hb : b ∈ Ioc x t)
    (hNoConnect : ArchesDoNotConnect (x, y) (a, b))
    (hOrientation : NestedArchesHaveSameOrientation (x, y) (a, b)) :
    False := by
  have hta : t < a := by
    apply lt_of_not_ge
    intro hat
    exact haPrefix ⟨ha.1, hat⟩
  have hba : b < a := hb.2.trans_lt hta
  have hxy : x < y := ht.1.trans ht.2
  have hLengths : 0 < min |y - x| |b - a| := by
    apply lt_min
    · exact abs_pos.mpr (sub_ne_zero.mpr hxy.ne')
    · exact abs_pos.mpr (sub_ne_zero.mpr hba.ne)
  have hya : y ≠ a := hNoConnect hLengths
  have hay : a < y := lt_of_le_of_ne ha.2 hya.symm
  have hStrictSubset : uIcc a b ⊆ uIoo x y := by
    intro r hr
    rw [uIcc_comm, uIcc_of_le hba.le] at hr
    rw [uIoo_of_le hxy.le]
    exact ⟨hb.1.trans_le hr.1, hr.2.trans_lt hay⟩
  have hSameDirection := hOrientation hStrictSubset
  have hForward : 0 < y - x := sub_pos.mpr hxy
  have hBackward : b - a < 0 := sub_neg.mpr hba
  exact (not_lt_of_ge hSameDirection)
    (mul_neg_of_pos_of_neg hForward hBackward)

theorem solution
    (rho : FiniteMeasure (Real × Real))
    (S : Set (Real × Real))
    (hFull : ∀ᵐ z ∂(rho : Measure (Real × Real)), z ∈ S)
    (hMonotone : IsMonotoneArchSet S)
    {x y t : Real}
    (hArch : (x, y) ∈ S)
    (ht : t ∈ Ioo x y) :
    (rho : Measure (Real × Real)) ((Icc x t)ᶜ ×ˢ Ioc x t) = 0 := by
  have hxy : x < y := ht.1.trans ht.2
  have hEquation15 :
      (rho : Measure (Real × Real)) ((Icc x y)ᶜ ×ˢ Ioo x y) = 0 :=
    (monotoneArchEquation15 rho S hFull hMonotone hArch hxy).1
  have hEquation15Avoid :
      ∀ᵐ z ∂(rho : Measure (Real × Real)),
        z ∉ (Icc x y)ᶜ ×ˢ Ioo x y := by
    simpa only [ae_iff, Classical.not_not, setOf_mem_eq] using hEquation15
  have hAvoid :
      ∀ᵐ z ∂(rho : Measure (Real × Real)),
        z ∉ (Icc x t)ᶜ ×ˢ Ioc x t := by
    filter_upwards [hFull, hEquation15Avoid] with z hzS hzEquation15
    intro hzPrefix
    by_cases hzFirst : z.1 ∈ Icc x y
    · have hConditions := hMonotone (x, y) hArch z hzS
      exact internalBackwardArchImpossible ht hzFirst hzPrefix.1 hzPrefix.2
        hConditions.2.1 hConditions.2.2
    · apply hzEquation15
      exact ⟨hzFirst, hzPrefix.2.1, hzPrefix.2.2.trans_lt ht.2⟩
  simpa only [ae_iff, Classical.not_not, setOf_mem_eq] using hAvoid

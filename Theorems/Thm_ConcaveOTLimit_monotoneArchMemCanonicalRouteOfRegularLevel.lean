import Theorems.Thm_ConcaveOTLimit_monotoneArchEndpointRigidity

open MeasureTheory Set

namespace ConcaveOTLimit

/-- A strict forward arch at a positive locally regular cumulative level
belongs to `juilletCanonicalRouteSet`. This only proves membership in the
declared relaxed local route set; it does not supply Juillet's global
regular-level finiteness, alternation, or canonical coupling construction. -/
theorem monotoneArchMemCanonicalRouteOfRegularLevel
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hForward : IsForwardPlan gamma)
    (S : Set (Real × Real))
    (hFull : IsSupported gamma S)
    (hMonotone : IsMonotoneArchSet S)
    {x y : Real}
    (hArch : (x, y) ∈ S)
    (hxy : x < y)
    (hPositive : 0 < signedCumulative mu nu x)
    (hRegularOnClosedArch :
      ∀ z ∈ Icc x y,
        (z, signedCumulative mu nu x) ∈
            generalizedCumulativeGraph mu nu ->
          IsGoodIncreasingCrossing
              mu nu z (signedCumulative mu nu x) ∨
            IsGoodDecreasingCrossing
              mu nu z (signedCumulative mu nu x)) :
    (x, y) ∈ juilletCanonicalRouteSet mu nu := by
  have hCertificate :=
    monotoneArchCumulativeCertificate
      gamma hAtomless hForward S hFull hMonotone hArch hxy
  have hSourceGraph :
      (x, signedCumulative mu nu x) ∈
        generalizedCumulativeGraph mu nu := by
    change
      signedCumulative mu nu x ∈
        uIcc (signedCumulativeLeft mu nu x)
          (signedCumulative mu nu x)
    exact right_mem_uIcc
  have hSourceIncreasing :
      IsGoodIncreasingCrossing
        mu nu x (signedCumulative mu nu x) := by
    rcases hRegularOnClosedArch x ⟨le_rfl, hxy.le⟩ hSourceGraph with
      hIncreasing | hDecreasing
    · exact hIncreasing
    · exfalso
      rcases hDecreasing with
        ⟨_hGraph, epsilon, hEpsilon, hLocal⟩
      have hRightBound :
          x < min y (x + epsilon) :=
        lt_min hxy (lt_add_of_pos_right x hEpsilon)
      obtain ⟨z, hxz, hzUpper⟩ :=
        exists_between hRightBound
      have hzy : z < y :=
        hzUpper.trans_le (min_le_left y (x + epsilon))
      have hNearUpper : z < x + epsilon :=
        hzUpper.trans_le (min_le_right y (x + epsilon))
      have hzArch : z ∈ Ioo x y := ⟨hxz, hzy⟩
      have hzNear : z ∈ Ioo (x - epsilon) (x + epsilon) :=
        ⟨(sub_lt_self x hEpsilon).trans hxz, hNearUpper⟩
      have hLevelLe :
          signedCumulative mu nu x <= signedCumulative mu nu z :=
        hCertificate.1 z hzArch
      have hzGraph :
          (z, signedCumulative mu nu z) ∈
            generalizedCumulativeGraph mu nu := by
        change
          signedCumulative mu nu z ∈
            uIcc (signedCumulativeLeft mu nu z)
              (signedCumulative mu nu z)
        exact right_mem_uIcc
      have hProduct := hLocal hzNear hxz.ne' hzGraph
      have hFirstFactor :
          0 <=
            signedCumulative mu nu z -
              signedCumulative mu nu x :=
        sub_nonneg.mpr hLevelLe
      have hSecondFactor : 0 <= z - x :=
        sub_nonneg.mpr hxz.le
      exact
        (not_lt_of_ge
          (mul_nonneg hFirstFactor hSecondFactor)) hProduct
  have hTargetDecreasing :
      IsGoodDecreasingCrossing
        mu nu y (signedCumulative mu nu x) := by
    rcases
        hRegularOnClosedArch y ⟨hxy.le, le_rfl⟩ hCertificate.2 with
      hIncreasing | hDecreasing
    · exfalso
      rcases hIncreasing with
        ⟨_hGraph, epsilon, hEpsilon, hLocal⟩
      have hLeftBound :
          max x (y - epsilon) < y :=
        max_lt hxy (sub_lt_self y hEpsilon)
      obtain ⟨z, hzLower, hzy⟩ :=
        exists_between hLeftBound
      have hxz : x < z :=
        (le_max_left x (y - epsilon)).trans_lt hzLower
      have hNearLower : y - epsilon < z :=
        (le_max_right x (y - epsilon)).trans_lt hzLower
      have hzArch : z ∈ Ioo x y := ⟨hxz, hzy⟩
      have hzNear : z ∈ Ioo (y - epsilon) (y + epsilon) :=
        ⟨hNearLower,
          hzy.trans (lt_add_of_pos_right y hEpsilon)⟩
      have hLevelLe :
          signedCumulative mu nu x <= signedCumulative mu nu z :=
        hCertificate.1 z hzArch
      have hzGraph :
          (z, signedCumulative mu nu z) ∈
            generalizedCumulativeGraph mu nu := by
        change
          signedCumulative mu nu z ∈
            uIcc (signedCumulativeLeft mu nu z)
              (signedCumulative mu nu z)
        exact right_mem_uIcc
      have hProduct := hLocal hzNear hzy.ne hzGraph
      have hFirstFactor :
          0 <=
            signedCumulative mu nu z -
              signedCumulative mu nu x :=
        sub_nonneg.mpr hLevelLe
      have hSecondFactor : z - y <= 0 :=
        sub_nonpos.mpr hzy.le
      exact
        (not_lt_of_ge
          (mul_nonpos_of_nonneg_of_nonpos
            hFirstFactor hSecondFactor)) hProduct
    · exact hDecreasing
  have hRegularOnArch :
      ∀ z ∈ Ioo x y,
        (z, signedCumulative mu nu x) ∈
            generalizedCumulativeGraph mu nu ->
          IsGoodIncreasingCrossing
              mu nu z (signedCumulative mu nu x) ∨
            IsGoodDecreasingCrossing
              mu nu z (signedCumulative mu nu x) := by
    intro z hz hGraph
    exact
      hRegularOnClosedArch z ⟨hz.1.le, hz.2.le⟩ hGraph
  have hConsecutive :
      AreConsecutiveAtLevel
        mu nu (signedCumulative mu nu x) x y :=
    (monotoneArchEndpointRigidity
      gamma hAtomless hForward S hFull hMonotone hArch hxy
      hRegularOnArch).1
  change
    ∃ h : Real,
      0 < h ∧
        IsGoodIncreasingCrossing mu nu x h ∧
          IsGoodDecreasingCrossing mu nu y h ∧
            AreConsecutiveAtLevel mu nu h x y
  exact
    ⟨signedCumulative mu nu x, hPositive, hSourceIncreasing,
      hTargetDecreasing, hConsecutive⟩

end ConcaveOTLimit

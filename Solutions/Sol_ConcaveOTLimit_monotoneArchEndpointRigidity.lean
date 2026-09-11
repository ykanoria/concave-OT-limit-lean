import Theorems.Thm_ConcaveOTLimit_monotoneArchCumulativeCertificate
import Theorems.Thm_ConcaveOTLimit_consecutiveAtLevelRightUnique

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
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
    (hRegularOnArch :
      ∀ z ∈ Ioo x y,
        (z, signedCumulative mu nu x) ∈
            generalizedCumulativeGraph mu nu ->
          IsGoodIncreasingCrossing
              mu nu z (signedCumulative mu nu x) ∨
            IsGoodDecreasingCrossing
              mu nu z (signedCumulative mu nu x)) :
    AreConsecutiveAtLevel
        mu nu (signedCumulative mu nu x) x y ∧
      ∀ y',
        AreConsecutiveAtLevel
            mu nu (signedCumulative mu nu x) x y' ->
          y' = y := by
  have hCertificate :=
    monotoneArchCumulativeCertificate
      gamma hAtomless hForward S hFull hMonotone hArch hxy
  have hConsecutive :
      AreConsecutiveAtLevel
        mu nu (signedCumulative mu nu x) x y := by
    refine ⟨hxy, ?_, hCertificate.2, ?_⟩
    · change
        signedCumulative mu nu x ∈
          uIcc (signedCumulativeLeft mu nu x)
            (signedCumulative mu nu x)
      exact right_mem_uIcc
    · intro z hz hGraph
      rcases hRegularOnArch z hz hGraph with
        hIncreasing | hDecreasing
      · rcases hIncreasing with
          ⟨_hGraph, epsilon, hEpsilon, hLocal⟩
        have hLeftBound :
            max x (z - epsilon) < z :=
          max_lt hz.1 (sub_lt_self z hEpsilon)
        obtain ⟨z', hz'Lower, hz'Upper⟩ :=
          exists_between hLeftBound
        have hxz' : x < z' :=
          (le_max_left x (z - epsilon)).trans_lt hz'Lower
        have hNearLower : z - epsilon < z' :=
          (le_max_right x (z - epsilon)).trans_lt hz'Lower
        have hz'Arch : z' ∈ Ioo x y :=
          ⟨hxz', hz'Upper.trans hz.2⟩
        have hz'Near : z' ∈ Ioo (z - epsilon) (z + epsilon) :=
          ⟨hNearLower,
            hz'Upper.trans (lt_add_of_pos_right z hEpsilon)⟩
        have hLevelLe :
            signedCumulative mu nu x <=
              signedCumulative mu nu z' :=
          hCertificate.1 z' hz'Arch
        have hz'Graph :
            (z', signedCumulative mu nu z') ∈
              generalizedCumulativeGraph mu nu := by
          change
            signedCumulative mu nu z' ∈
              uIcc (signedCumulativeLeft mu nu z')
                (signedCumulative mu nu z')
          exact right_mem_uIcc
        have hProduct :=
          hLocal hz'Near hz'Upper.ne hz'Graph
        have hFirstFactor :
            0 <=
              signedCumulative mu nu z' -
                signedCumulative mu nu x :=
          sub_nonneg.mpr hLevelLe
        have hSecondFactor :
            z' - z <= 0 :=
          sub_nonpos.mpr hz'Upper.le
        exact
          (not_lt_of_ge
            (mul_nonpos_of_nonneg_of_nonpos
              hFirstFactor hSecondFactor)) hProduct
      · rcases hDecreasing with
          ⟨_hGraph, epsilon, hEpsilon, hLocal⟩
        have hRightBound :
            z < min y (z + epsilon) :=
          lt_min hz.2 (lt_add_of_pos_right z hEpsilon)
        obtain ⟨z', hz'Lower, hz'Upper⟩ :=
          exists_between hRightBound
        have hz'y : z' < y :=
          hz'Upper.trans_le (min_le_left y (z + epsilon))
        have hNearUpper : z' < z + epsilon :=
          hz'Upper.trans_le (min_le_right y (z + epsilon))
        have hz'Arch : z' ∈ Ioo x y :=
          ⟨hz.1.trans hz'Lower, hz'y⟩
        have hz'Near : z' ∈ Ioo (z - epsilon) (z + epsilon) :=
          ⟨(sub_lt_self z hEpsilon).trans hz'Lower, hNearUpper⟩
        have hLevelLe :
            signedCumulative mu nu x <=
              signedCumulative mu nu z' :=
          hCertificate.1 z' hz'Arch
        have hz'Graph :
            (z', signedCumulative mu nu z') ∈
              generalizedCumulativeGraph mu nu := by
          change
            signedCumulative mu nu z' ∈
              uIcc (signedCumulativeLeft mu nu z')
                (signedCumulative mu nu z')
          exact right_mem_uIcc
        have hProduct :=
          hLocal hz'Near hz'Lower.ne' hz'Graph
        have hFirstFactor :
            0 <=
              signedCumulative mu nu z' -
                signedCumulative mu nu x :=
          sub_nonneg.mpr hLevelLe
        have hSecondFactor :
            0 <= z' - z :=
          sub_nonneg.mpr hz'Lower.le
        exact
          (not_lt_of_ge
            (mul_nonneg hFirstFactor hSecondFactor)) hProduct
  refine ⟨hConsecutive, ?_⟩
  intro y' hConsecutive'
  exact
    (consecutiveAtLevelRightUnique
      mu nu (signedCumulative mu nu x) x y y'
      hConsecutive hConsecutive').symm

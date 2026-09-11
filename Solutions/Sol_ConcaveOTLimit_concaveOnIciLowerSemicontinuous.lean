import Definitions.Def_ConcaveOTLimitModel
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.Semicontinuity.Basic

open Filter Set Topology

open ConcaveOTLimit

theorem solution
    {profile : Real -> Real}
    (hConcave : ConcaveOn Real (Ici 0) profile) :
    LowerSemicontinuousOn profile (Ici 0) := by
  intro x hx
  change 0 <= x at hx
  rcases hx.eq_or_lt with rfl | hxPositive
  · intro r hr
    let affine : Real -> Real :=
      fun t => (1 - t) * profile 0 + t * profile 1
    have hAffineContinuous : Continuous affine := by
      dsimp [affine]
      fun_prop
    have hAffineZero : r < affine 0 := by
      simpa [affine] using hr
    have hEventuallyAffine :
        ∀ᶠ t in nhds 0, r < affine t :=
      hAffineContinuous.continuousAt (Ioi_mem_nhds hAffineZero)
    have hEventuallyLtOne :
        ∀ᶠ t : Real in nhds 0, t < 1 :=
      Iio_mem_nhds zero_lt_one
    filter_upwards
      [hEventuallyAffine.filter_mono inf_le_left,
        self_mem_nhdsWithin,
        hEventuallyLtOne.filter_mono inf_le_left]
        with t hrt htNonnegative htOne
    have hChord :=
      hConcave.2
        (show (0 : Real) ∈ Ici 0 by simp)
        (show (1 : Real) ∈ Ici 0 by simp)
        (sub_nonneg.mpr htOne.le) htNonnegative
        (by ring : (1 - t) + t = (1 : Real))
    have hAffineLe : affine t <= profile t := by
      simpa [affine, smul_eq_mul] using hChord
    exact hrt.trans_le hAffineLe
  · have hxInterior : x ∈ interior (Ici (0 : Real)) := by
      simpa only [interior_Ici, mem_Ioi] using hxPositive
    have hContinuousAt : ContinuousAt profile x :=
      (hConcave.continuousOn_interior x hxInterior).continuousAt
        (IsOpen.mem_nhds isOpen_interior hxInterior)
    exact hContinuousAt.lowerSemicontinuousAt.lowerSemicontinuousWithinAt _

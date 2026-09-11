import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileHasNonnegativeLscDistanceShift
import Theorems.Thm_ConcaveOTLimit_lowerSemicontinuousExtendTopOutsideClosed

open Set Topology

namespace ConcaveOTLimit

/-- An admissible concave profile admits a nonnegative affine shift whose
`ENNReal` cost, restricted to forward pairs and extended by `top`, is lower
semicontinuous. -/
theorem admissibleConcaveRestrictedShiftLowerSemicontinuous
    {profile : Real -> Real}
    (hProfile : AdmissibleConcaveProfile profile) :
    exists C : Real, 0 <= C /\
      (forall x y : Real,
        0 <= profile ‖x - y‖ + C * (1 + ‖x - y‖)) /\
      LowerSemicontinuous
        (fun z : Real × Real =>
          if z.1 <= z.2 then
            ENNReal.ofReal
              (profile ‖z.1 - z.2‖ + C * (1 + ‖z.1 - z.2‖))
          else ⊤) := by
  obtain ⟨C, hC, hNonnegative, hLower⟩ :=
    admissibleConcaveProfileHasNonnegativeLscDistanceShift
      (E := Real) hProfile
  refine ⟨C, hC, hNonnegative, ?_⟩
  let shifted : Real × Real -> Real :=
    fun z => profile ‖z.1 - z.2‖ + C * (1 + ‖z.1 - z.2‖)
  have hOfReal :
      LowerSemicontinuous (fun z => ENNReal.ofReal (shifted z)) := by
    simpa [Function.comp_def] using
      ENNReal.continuous_ofReal.comp_lowerSemicontinuous
        hLower ENNReal.ofReal_mono
  let forward : Set (Real × Real) := {z | z.1 <= z.2}
  have hForward : IsClosed forward := by
    simpa [forward] using
      (isClosed_le continuous_fst continuous_snd :
        IsClosed {z : Real × Real | z.1 <= z.2})
  simpa [shifted, forward] using
    lowerSemicontinuousExtendTopOutsideClosed hOfReal hForward

end ConcaveOTLimit

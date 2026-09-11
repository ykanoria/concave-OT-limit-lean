import Theorems.Thm_ConcaveOTLimit_concaveOnIciLowerSemicontinuous

open Set Topology

namespace ConcaveOTLimit

/-- The affine lower control in an admissible concave profile produces a
nonnegative lower-semicontinuous shift on nonnegative distances. -/
theorem admissibleConcaveProfileHasNonnegativeLscShift
    {profile : Real -> Real}
    (hProfile : AdmissibleConcaveProfile profile) :
    exists C : Real, 0 <= C /\
      (forall {d : Real}, 0 <= d ->
        0 <= profile d + C * (1 + d)) /\
      LowerSemicontinuousOn
        (fun d => profile d + C * (1 + d)) (Ici 0) := by
  rcases hProfile with
    ⟨hConcave, C, hCNonnegative, hLower⟩
  refine ⟨C, hCNonnegative, ?_, ?_⟩
  · intro d hd
    linarith [hLower hd]
  · have hAffineContinuous :
        Continuous (fun d : Real => C * (1 + d)) := by
      fun_prop
    exact
      (concaveOnIciLowerSemicontinuous hConcave).add
        (hAffineContinuous.lowerSemicontinuous.lowerSemicontinuousOn (Ici 0))

end ConcaveOTLimit

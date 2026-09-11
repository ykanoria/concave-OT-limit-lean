import Theorems.Thm_ConcaveOTLimit_admissibleConcaveProfileHasNonnegativeLscShift

open Set Topology

namespace ConcaveOTLimit

/-- An admissible concave profile can be shifted to give a nonnegative,
lower-semicontinuous integrand on pairs. -/
theorem admissibleConcaveProfileHasNonnegativeLscDistanceShift
    {E : Type*} [NormedAddCommGroup E]
    {profile : Real -> Real}
    (hProfile : AdmissibleConcaveProfile profile) :
    exists C : Real, 0 <= C /\
      (forall x y : E,
        0 <= profile ‖x - y‖ + C * (1 + ‖x - y‖)) /\
      LowerSemicontinuous
        (fun z : E × E =>
          profile ‖z.1 - z.2‖ + C * (1 + ‖z.1 - z.2‖)) := by
  obtain ⟨C, hC, hNonnegative, hLowerSemicontinuous⟩ :=
    admissibleConcaveProfileHasNonnegativeLscShift hProfile
  refine ⟨C, hC, ?_, ?_⟩
  · intro x y
    exact hNonnegative (norm_nonneg (x - y))
  · let distance : E × E -> Real :=
      fun z => ‖z.1 - z.2‖
    have hDistanceContinuous : Continuous distance := by
      simpa [distance] using
        (continuous_fst.sub continuous_snd).norm
    have hDistanceMaps :
        MapsTo distance (Set.univ : Set (E × E)) (Ici 0) := by
      intro z _hz
      exact norm_nonneg _
    rw [← lowerSemicontinuousOn_univ_iff]
    simpa [distance, Function.comp_def] using
      hLowerSemicontinuous.comp
        hDistanceContinuous.continuousOn hDistanceMaps

end ConcaveOTLimit

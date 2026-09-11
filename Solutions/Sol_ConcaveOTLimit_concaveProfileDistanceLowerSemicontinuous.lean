import Theorems.Thm_ConcaveOTLimit_concaveOnIciLowerSemicontinuous

open Set Topology

open ConcaveOTLimit

theorem solution
    {E : Type*} [NormedAddCommGroup E]
    {profile : Real -> Real}
    (hConcave : ConcaveOn Real (Ici 0) profile) :
    LowerSemicontinuous
      (fun z : E × E => profile ‖z.1 - z.2‖) := by
  let distance : E × E -> Real :=
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
    (concaveOnIciLowerSemicontinuous hConcave).comp
      hDistanceContinuous.continuousOn hDistanceMaps

import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

open Filter MeasureTheory Set Topology

theorem solution
    {Omega : Type*} [MeasurableSpace Omega] [TopologicalSpace Omega]
    [TopologicalSpace.PseudoMetrizableSpace Omega]
    [TopologicalSpace.SeparableSpace Omega]
    [OpensMeasurableSpace Omega]
    {f : Omega -> Real}
    (hLower : LowerSemicontinuous f)
    (hNonnegative : 0 <= f) :
    LowerSemicontinuous
      (fun P : ProbabilityMeasure Omega =>
        ∫⁻ x, ENNReal.ofReal (f x) ∂(P : Measure Omega)) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro P
  simp_rw [lintegral_eq_lintegral_meas_lt _
    (Eventually.of_forall hNonnegative)
    hLower.measurable.aemeasurable]
  calc
    ∫⁻ (t : Real) in Ioi 0, (P : Measure Omega) {x | t < f x} <=
        ∫⁻ (t : Real) in Ioi 0,
          (nhds P).liminf
            (fun Q : ProbabilityMeasure Omega =>
              (Q : Measure Omega) {x | t < f x}) := by
      exact lintegral_mono (fun t =>
        ProbabilityMeasure.le_liminf_measure_open_of_tendsto
          (μ := P) (μs := fun Q : ProbabilityMeasure Omega => Q)
          tendsto_id (hLower.isOpen_preimage t))
    _ <=
        (nhds P).liminf
          (fun Q : ProbabilityMeasure Omega =>
            ∫⁻ (t : Real) in Ioi 0,
              (Q : Measure Omega) {x | t < f x}) := by
      exact lintegral_liminf_le
        (fun Q => Antitone.measurable
          (fun s t hst => measure_mono
            (fun x hx => lt_of_le_of_lt hst hx)))

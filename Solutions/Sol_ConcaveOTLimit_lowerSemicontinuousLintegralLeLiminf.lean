import Mathlib.MeasureTheory.Measure.Portmanteau

open Filter MeasureTheory Set Topology

theorem solution
    {Omega I : Type*} [MeasurableSpace Omega] [TopologicalSpace Omega]
    [OpensMeasurableSpace Omega]
    {L : Filter I} {mu : Measure Omega} {muSeq : I -> Measure Omega}
    [L.IsCountablyGenerated]
    {f : Omega -> Real}
    (hLower : LowerSemicontinuous f)
    (hNonnegative : 0 <= f)
    (hOpen :
      forall G : Set Omega, IsOpen G ->
        mu G <= L.liminf (fun i => muSeq i G)) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂mu) <=
      L.liminf
        (fun i => ∫⁻ x, ENNReal.ofReal (f x) ∂(muSeq i)) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _
    (Eventually.of_forall hNonnegative)
    hLower.measurable.aemeasurable]
  calc
    ∫⁻ (t : Real) in Ioi 0, mu {x | t < f x} <=
        ∫⁻ (t : Real) in Ioi 0,
          L.liminf (fun i => muSeq i {x | t < f x}) := by
      exact (lintegral_mono
        (fun t => hOpen _ (hLower.isOpen_preimage t))).trans (le_refl _)
    _ <=
        L.liminf
          (fun i => ∫⁻ (t : Real) in Ioi 0, muSeq i {x | t < f x}) := by
      exact lintegral_liminf_le
        (fun i => Antitone.measurable
          (fun s t hst => measure_mono
            (fun x hx => lt_of_le_of_lt hst hx)))

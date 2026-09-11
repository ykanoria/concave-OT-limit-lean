import Mathlib.MeasureTheory.Measure.Portmanteau

open Filter MeasureTheory Set Topology

namespace ConcaveOTLimit

private theorem leMeasureComplLiminfOfLimsupMeasureLeOfUnivEq
    {Omega I : Type*} [MeasurableSpace Omega]
    {L : Filter I} {mu : Measure Omega} {muSeq : I -> Measure Omega}
    [IsFiniteMeasure mu] [forall i, IsFiniteMeasure (muSeq i)]
    {s : Set Omega} (hs : MeasurableSet s)
    (hUniv : forall i, muSeq i univ = mu univ)
    (hLimsup : L.limsup (fun i => muSeq i s) <= mu s) :
    mu sᶜ <= L.liminf (fun i => muSeq i sᶜ) := by
  rcases L.eq_or_neBot with rfl | hL
  · simp only [liminf_bot, le_top]
  have hMuCompl : mu sᶜ = mu univ - mu s :=
    measure_compl hs (measure_lt_top mu s).ne
  have hMuSeqCompl : forall i, muSeq i sᶜ = mu univ - muSeq i s := by
    intro i
    rw [measure_compl hs (measure_lt_top (muSeq i) s).ne, hUniv i]
  simp_rw [hMuCompl, hMuSeqCompl]
  rw [show (L.liminf fun i : I => mu univ - muSeq i s) =
      L.liminf ((fun x => mu univ - x) ∘ fun i : I => muSeq i s) from rfl]
  have hMap := antitone_const_tsub.map_limsup_of_continuousAt (F := L)
    (fun i => muSeq i s)
    (ENNReal.continuous_sub_left (measure_ne_top mu univ)).continuousAt
  simpa [← hMap] using antitone_const_tsub hLimsup

/-- Weak convergence of finite measures with equal total mass gives the
Portmanteau lower bound on open sets. -/
theorem finiteMeasureLeLiminfMeasureOpenOfTendstoOfMassEq
    {Omega I : Type*} [MeasurableSpace Omega] [TopologicalSpace Omega]
    [OpensMeasurableSpace Omega] [HasOuterApproxClosed Omega]
    {L : Filter I} {mu : FiniteMeasure Omega}
    {muSeq : I -> FiniteMeasure Omega}
    (hTendsto : Tendsto muSeq L (nhds mu))
    (hMass : forall i, (muSeq i).mass = mu.mass)
    {G : Set Omega} (hG : IsOpen G) :
    (mu : Measure Omega) G <=
      L.liminf (fun i => (muSeq i : Measure Omega) G) := by
  have hUniv : forall i, (muSeq i : Measure Omega) univ =
      (mu : Measure Omega) univ := by
    intro i
    rw [← FiniteMeasure.ennreal_mass, ← FiniteMeasure.ennreal_mass, hMass i]
  have hClosed :
      L.limsup (fun i => (muSeq i : Measure Omega) Gᶜ) <=
        (mu : Measure Omega) Gᶜ :=
    FiniteMeasure.limsup_measure_closed_le_of_tendsto hTendsto
      (isClosed_compl_iff.mpr hG)
  simpa only [compl_compl] using
    leMeasureComplLiminfOfLimsupMeasureLeOfUnivEq
      hG.measurableSet.compl hUniv hClosed

end ConcaveOTLimit

import Definitions.Def_ConcaveOTLimitModel
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.MetricSpace.Polish

open Filter MeasureTheory Set Topology

open ConcaveOTLimit

private theorem measurePreservingFst
    {mu nu : FiniteMeasure Real} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.fst
      (gamma.plan : Measure (Real × Real)) (mu : Measure Real) := by
  refine ⟨measurable_fst, ?_⟩
  simpa [firstMarginal] using congrArg
    (fun eta : FiniteMeasure Real => (eta : Measure Real)) gamma.property.1

private theorem planUnivEqSourceUniv
    {mu nu : FiniteMeasure Real} (gamma : FiniteCoupling mu nu) :
    (gamma.plan : Measure (Real × Real)) univ =
      (mu : Measure Real) univ := by
  calc
    (gamma.plan : Measure (Real × Real)) univ =
        Measure.map Prod.fst
          (gamma.plan : Measure (Real × Real)) univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ]
      simp
    _ = (mu : Measure Real) univ := by
      rw [(measurePreservingFst gamma).map_eq]

theorem solution
    {mu nu : FiniteMeasure Real} :
    IsClosed {gamma : FiniteCoupling mu nu | IsForwardPlan gamma} := by
  rw [isClosed_iff_forall_filter]
  intro gamma L hLNontrivial hLForward hLGamma
  letI : NeBot L := hLNontrivial
  let forwardSet : Set (Real × Real) := {z | z.1 <= z.2}
  have hForwardSetClosed : IsClosed forwardSet :=
    isClosed_le continuous_fst continuous_snd
  have hEventuallyForward :
      ∀ᶠ eta in L, IsForwardPlan eta := by
    apply hLForward
    simp
  have hPlanTendsto :
      Tendsto (fun eta : FiniteCoupling mu nu => eta.plan)
        L (nhds gamma.plan) := by
    simpa [FiniteCoupling.plan] using
      (continuous_subtype_val.tendsto gamma).mono_left hLGamma
  have hPortmanteau :=
    FiniteMeasure.limsup_measure_closed_le_of_tendsto
      hPlanTendsto hForwardSetClosed
  have hEventuallyMass :
      ∀ᶠ eta in L,
        (eta.plan : Measure (Real × Real)) forwardSet =
          (mu : Measure Real) univ := by
    filter_upwards [hEventuallyForward] with eta hEta
    calc
      (eta.plan : Measure (Real × Real)) forwardSet =
          (eta.plan : Measure (Real × Real)) univ :=
        (ae_mem_iff_measure_eq
          hForwardSetClosed.measurableSet.nullMeasurableSet).mp hEta
      _ = (mu : Measure Real) univ := planUnivEqSourceUniv eta
  have hMassLe :
      (mu : Measure Real) univ <=
        (gamma.plan : Measure (Real × Real)) forwardSet := by
    calc
      (mu : Measure Real) univ =
          L.limsup
            (fun _eta : FiniteCoupling mu nu =>
              (mu : Measure Real) univ) := by
        simp only [limsup_const]
      _ = L.limsup
            (fun eta : FiniteCoupling mu nu =>
              (eta.plan : Measure (Real × Real)) forwardSet) :=
        (limsup_congr hEventuallyMass).symm
      _ <= (gamma.plan : Measure (Real × Real)) forwardSet :=
        hPortmanteau
  apply
    (ae_mem_iff_measure_eq
      hForwardSetClosed.measurableSet.nullMeasurableSet).mpr
  apply le_antisymm (measure_mono (subset_univ forwardSet))
  calc
    (gamma.plan : Measure (Real × Real)) univ =
        (mu : Measure Real) univ :=
      planUnivEqSourceUniv gamma
    _ <= (gamma.plan : Measure (Real × Real)) forwardSet := hMassLe

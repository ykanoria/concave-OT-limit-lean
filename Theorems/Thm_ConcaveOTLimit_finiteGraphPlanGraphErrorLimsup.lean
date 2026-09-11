import Definitions.Def_ConcaveOTLimitModel
import Mathlib.MeasureTheory.Measure.Portmanteau

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace ConcaveOTLimit

/-- Weak convergence of finite graph plans forces the restricted pointwise
error masses to have limsup zero on a closed continuity set. -/
theorem finiteGraphPlanGraphErrorLimsup
    {X Y I : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    {L : Filter I} (mu : FiniteMeasure X)
    (S : I -> X -> Y) (T : X -> Y)
    (hS : forall i, Measurable (S i)) (hT : Measurable T)
    (K : Set X) (hK : IsClosed K) (hT_on : ContinuousOn T K)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hgraph :
      Tendsto (fun i => finiteGraphPlan mu (S i) (hS i)) L
        (nhds (finiteGraphPlan mu T hT))) :
    L.limsup (fun i =>
      (mu : Measure X)
        ({x | epsilon <= dist (S i x) (T x)} ∩ K)) <= 0 := by
  let F : Set (X × Y) :=
    {p | p.1 ∈ K /\ epsilon <= dist p.2 (T p.1)}
  have hdomain : IsClosed (K ×ˢ (univ : Set Y)) :=
    hK.prod isClosed_univ
  have hT_fst :
      ContinuousOn (fun p : X × Y => T p.1) (K ×ˢ (univ : Set Y)) :=
    hT_on.comp continuousOn_fst (fun _ hp => hp.1)
  have hdist :
      ContinuousOn
        (fun p : X × Y => dist p.2 (T p.1))
        (K ×ˢ (univ : Set Y)) :=
    continuous_dist.comp_continuousOn (continuousOn_snd.prodMk hT_fst)
  have hF_closed : IsClosed F := by
    have hclosed :
        IsClosed
          ((K ×ˢ (univ : Set Y)) ∩
            (fun p : X × Y => dist p.2 (T p.1)) ⁻¹' Ici epsilon) :=
      hdist.preimage_isClosed_of_isClosed hdomain isClosed_Ici
    rw [show F =
        (K ×ˢ (univ : Set Y)) ∩
          (fun p : X × Y => dist p.2 (T p.1)) ⁻¹' Ici epsilon by
      ext p
      constructor
      · rintro ⟨hpK, hpdist⟩
        exact ⟨⟨hpK, mem_univ _⟩, hpdist⟩
      · rintro ⟨⟨hpK, _⟩, hpdist⟩
        exact ⟨hpK, hpdist⟩]
    exact hclosed
  have hgraph_mass (R : X -> Y) (hR : Measurable R) :
      ((finiteGraphPlan mu R hR : FiniteMeasure (X × Y)) :
        Measure (X × Y)) F =
        (mu : Measure X)
          ({x | epsilon <= dist (R x) (T x)} ∩ K) := by
    have hpair : Measurable (fun x : X => (x, R x)) :=
      measurable_id.prodMk hR
    simp only [finiteGraphPlan, FiniteMeasure.toMeasure_map]
    rw [Measure.map_apply hpair hF_closed.measurableSet]
    congr 1
    ext x
    simp [F, and_comm]
  have hlimit_zero :
      ((finiteGraphPlan mu T hT : FiniteMeasure (X × Y)) :
        Measure (X × Y)) F = 0 := by
    calc
      ((finiteGraphPlan mu T hT : FiniteMeasure (X × Y)) :
          Measure (X × Y)) F =
          (mu : Measure X)
            ({x | epsilon <= dist (T x) (T x)} ∩ K) :=
        hgraph_mass T hT
      _ = 0 := by simp [not_le_of_gt hepsilon]
  have hlimsup :
      L.limsup (fun i =>
        ((finiteGraphPlan mu (S i) (hS i) :
          FiniteMeasure (X × Y)) : Measure (X × Y)) F) <= 0 := by
    simpa only [hlimit_zero] using
      FiniteMeasure.limsup_measure_closed_le_of_tendsto hgraph hF_closed
  have hplan_error (i : I) :
      ((finiteGraphPlan mu (S i) (hS i) :
        FiniteMeasure (X × Y)) : Measure (X × Y)) F =
        (mu : Measure X)
          ({x | epsilon <= dist (S i x) (T x)} ∩ K) :=
    hgraph_mass (S i) (hS i)
  simpa only [hplan_error] using hlimsup

end ConcaveOTLimit

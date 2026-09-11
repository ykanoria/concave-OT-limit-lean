import Definitions.Def_ConcaveOTLimitModel

open MeasureTheory Set Topology

open ConcaveOTLimit

theorem solution
    {X Y : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    (mu : FiniteMeasure X) (S T : X -> Y) (hS : Measurable S)
    (K : Set X) (hK : IsClosed K) (hT : ContinuousOn T K)
    (epsilon : Real) :
    ((finiteGraphPlan mu S hS : FiniteMeasure (X × Y)) :
        Measure (X × Y))
        {p | p.1 ∈ K /\ epsilon <= dist p.2 (T p.1)} =
      (mu : Measure X)
        ({x | epsilon <= dist (S x) (T x)} ∩ K) := by
  let F : Set (X × Y) :=
    {p | p.1 ∈ K /\ epsilon <= dist p.2 (T p.1)}
  have hdomain : IsClosed (K ×ˢ (univ : Set Y)) :=
    hK.prod isClosed_univ
  have hT_fst :
      ContinuousOn (fun p : X × Y => T p.1) (K ×ˢ (univ : Set Y)) :=
    hT.comp continuousOn_fst (fun _ hp => hp.1)
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
  have hpair : Measurable (fun x : X => (x, S x)) :=
    measurable_id.prodMk hS
  change
    ((finiteGraphPlan mu S hS : FiniteMeasure (X × Y)) :
        Measure (X × Y)) F =
      (mu : Measure X)
        ({x | epsilon <= dist (S x) (T x)} ∩ K)
  simp only [finiteGraphPlan, FiniteMeasure.toMeasure_map]
  rw [Measure.map_apply hpair hF_closed.measurableSet]
  congr 1
  ext x
  simp [F, and_comm]

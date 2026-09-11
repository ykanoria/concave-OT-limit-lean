import Definitions.Def_ConcaveOTLimitModel
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau

open Filter MeasureTheory Set Topology
open scoped ENNReal

open ConcaveOTLimit

theorem solution
    {X Y I : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    {L : Filter I} (mu : FiniteMeasure X)
    (S : I -> X -> Y) (T : X -> Y)
    (hS : forall i, Measurable (S i)) (hT : Measurable T)
    (hLusin : forall delta : ENNReal, delta ≠ 0 ->
      exists K : Set X, IsClosed K /\ ContinuousOn T K /\
        (mu : Measure X) Kᶜ < delta)
    (hgraph :
      Tendsto (fun i => finiteGraphPlan mu (S i) (hS i)) L
        (nhds (finiteGraphPlan mu T hT))) :
    TendstoInMeasure (mu : Measure X) S L T := by
  rw [tendstoInMeasure_iff_dist]
  intro epsilon hepsilon
  rw [ENNReal.nhds_zero_basis.tendsto_right_iff]
  intro eta heta
  by_cases heta_top : eta = ∞
  · subst eta
    filter_upwards with i
    exact measure_lt_top (mu : Measure X)
      {x | epsilon <= dist (S i x) (T x)}
  have heta_half : eta / 2 ≠ 0 :=
    ENNReal.div_ne_zero.mpr ⟨heta.ne', ENNReal.ofNat_ne_top⟩
  obtain ⟨K, hK_closed, hT_cont, hK_small⟩ :=
    hLusin (eta / 2) heta_half
  let F : Set (X × Y) :=
    {p | p.1 ∈ K /\ epsilon <= dist p.2 (T p.1)}
  have hF_closed : IsClosed F := by
    have hdomain : IsClosed (K ×ˢ (univ : Set Y)) :=
      hK_closed.prod isClosed_univ
    have hT_fst :
        ContinuousOn (fun p : X × Y => T p.1)
          (K ×ˢ (univ : Set Y)) :=
      hT_cont.comp continuousOn_fst (fun _ hp => hp.1)
    have hdist :
        ContinuousOn (fun p : X × Y => dist p.2 (T p.1))
          (K ×ˢ (univ : Set Y)) :=
      continuous_dist.comp_continuousOn (continuousOn_snd.prodMk hT_fst)
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
  have hlimit_zero :
      ((finiteGraphPlan mu T hT : FiniteMeasure (X × Y)) :
        Measure (X × Y)) F = 0 := by
    have hpair : Measurable (fun x : X => (x, T x)) :=
      measurable_id.prodMk hT
    simp only [finiteGraphPlan, FiniteMeasure.toMeasure_map]
    rw [Measure.map_apply hpair hF_closed.measurableSet]
    simp [F, not_le_of_gt hepsilon]
  have hlimsup :
      L.limsup (fun i =>
        ((finiteGraphPlan mu (S i) (hS i) :
          FiniteMeasure (X × Y)) : Measure (X × Y)) F) <= 0 := by
    simpa [hlimit_zero] using
      FiniteMeasure.limsup_measure_closed_le_of_tendsto hgraph hF_closed
  have hgraph_eventually :
      ∀ᶠ i in L,
        ((finiteGraphPlan mu (S i) (hS i) :
          FiniteMeasure (X × Y)) : Measure (X × Y)) F < eta / 2 := by
    exact eventually_lt_of_limsup_lt
      (hlimsup.trans_lt (by positivity)) (by isBoundedDefault)
  filter_upwards [hgraph_eventually] with i hi
  have hmap :
      ((finiteGraphPlan mu (S i) (hS i) :
        FiniteMeasure (X × Y)) : Measure (X × Y)) F =
        (mu : Measure X)
          ({x | epsilon <= dist (S i x) (T x)} ∩ K) := by
    have hpair : Measurable (fun x : X => (x, S i x)) :=
      measurable_id.prodMk (hS i)
    simp only [finiteGraphPlan, FiniteMeasure.toMeasure_map]
    rw [Measure.map_apply hpair hF_closed.measurableSet]
    congr 1
    ext x
    simp [F, and_comm]
  calc
    (mu : Measure X) {x | epsilon <= dist (S i x) (T x)}
        <= (mu : Measure X)
              ({x | epsilon <= dist (S i x) (T x)} ∩ K) +
            (mu : Measure X) Kᶜ := by
          apply (measure_mono ?_).trans (measure_union_le _ _)
          intro x hx
          by_cases hxK : x ∈ K
          · exact Or.inl ⟨hx, hxK⟩
          · exact Or.inr hxK
    _ < eta / 2 + eta / 2 :=
      ENNReal.add_lt_add (hmap ▸ hi) hK_small
    _ = eta := ENNReal.add_halves eta

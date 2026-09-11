import Definitions.Def_ConcaveOTLimitModel

open Set Topology

open ConcaveOTLimit

theorem solution
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    (K : Set X) (T : X -> Y) (epsilon : Real)
    (hK : IsClosed K) (hT : ContinuousOn T K) :
    IsClosed {p : X × Y | p.1 ∈ K /\ epsilon <= dist p.2 (T p.1)} := by
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
  have hclosed :
      IsClosed
        ((K ×ˢ (univ : Set Y)) ∩
          (fun p : X × Y => dist p.2 (T p.1)) ⁻¹' Ici epsilon) :=
    hdist.preimage_isClosed_of_isClosed hdomain isClosed_Ici
  rw [show
      {p : X × Y | p.1 ∈ K /\ epsilon <= dist p.2 (T p.1)} =
        (K ×ˢ (univ : Set Y)) ∩
          (fun p : X × Y => dist p.2 (T p.1)) ⁻¹' Ici epsilon by
    ext p
    constructor
    · rintro ⟨hpK, hpdist⟩
      exact ⟨⟨hpK, mem_univ _⟩, hpdist⟩
    · rintro ⟨⟨hpK, _⟩, hpdist⟩
      exact ⟨hpK, hpdist⟩]
  exact hclosed

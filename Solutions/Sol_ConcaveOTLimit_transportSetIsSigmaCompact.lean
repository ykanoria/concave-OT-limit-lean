import Definitions.Def_ConcaveOTLimitModel

open Set

open ConcaveOTLimit

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {Gamma : Set (E × E)}
    (hGamma : IsSigmaCompact Gamma) :
    IsSigmaCompact (transportSet Gamma) := by
  let offDiagonal : Set (E × E) := {p | p.1 ≠ p.2}
  let segmentEvaluation : (E × E) × Real -> E :=
    fun q => AffineMap.lineMap q.1.1 q.1.2 q.2
  have hOffDiagonalOpen : IsOpen offDiagonal := by
    exact isOpen_ne_fun continuous_fst continuous_snd
  have hEvaluationContinuous : Continuous segmentEvaluation := by
    dsimp only [segmentEvaluation]
    fun_prop
  have hTransportImage :
      transportSet Gamma =
        segmentEvaluation ''
          ((Gamma ∩ offDiagonal) ×ˢ Ioo (0 : Real) 1) := by
    ext z
    constructor
    · rintro ⟨p, hpGamma, hpne, hzp⟩
      rw [openSegment_eq_image_lineMap] at hzp
      obtain ⟨t, ht, rfl⟩ := hzp
      exact ⟨(p, t), ⟨⟨hpGamma, hpne⟩, ht⟩, rfl⟩
    · rintro ⟨q, ⟨⟨hqGamma, hqne⟩, hqt⟩, rfl⟩
      exact ⟨q.1, hqGamma, hqne,
        lineMap_mem_openSegment Real q.1.1 q.1.2 hqt⟩
  have sigmaCompactProd :
      ∀ {s : Set (E × E)} {t : Set Real},
        IsSigmaCompact s -> IsSigmaCompact t ->
          IsSigmaCompact (s ×ˢ t) := by
    intro s t hs ht
    obtain ⟨K, hK, hKs⟩ := hs
    obtain ⟨L, hL, hLt⟩ := ht
    have hcover : s ×ˢ t = ⋃ i, ⋃ j, K i ×ˢ L j := by
      rw [← hKs, ← hLt]
      ext p
      simp only [mem_prod, mem_iUnion]
      constructor
      · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
        exact ⟨i, j, hi, hj⟩
      · rintro ⟨i, j, hi, hj⟩
        exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    rw [hcover]
    exact isSigmaCompact_iUnion _ fun i =>
      isSigmaCompact_iUnion _ fun j =>
        ((hK i).prod (hL j)).isSigmaCompact
  have sigmaCompactInterOpen :
      ∀ {s t : Set (E × E)},
        IsSigmaCompact s -> IsOpen t -> IsSigmaCompact (s ∩ t) := by
    intro s t hs ht
    obtain ⟨K, hK, hKs⟩ := hs
    obtain ⟨F, hFclosed, _hFsub, hFt, _hFmono⟩ :=
      ht.exists_iUnion_isClosed
    have hcover : s ∩ t = ⋃ i, ⋃ j, K i ∩ F j := by
      rw [← hKs, ← hFt]
      ext x
      simp only [mem_inter_iff, mem_iUnion]
      constructor
      · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
        exact ⟨i, j, hi, hj⟩
      · rintro ⟨i, j, hi, hj⟩
        exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    rw [hcover]
    exact isSigmaCompact_iUnion _ fun i =>
      isSigmaCompact_iUnion _ fun j =>
        ((hK i).inter_right (hFclosed j)).isSigmaCompact
  have sigmaCompactIoo :
      ∀ a b : Real, IsSigmaCompact (Ioo a b) := by
    intro a b
    obtain ⟨F, hFclosed, hFsub, hFunion, _hFmono⟩ :=
      (isOpen_Ioo : IsOpen (Ioo a b)).exists_iUnion_isClosed
    refine ⟨F, ?_, hFunion⟩
    intro i
    exact IsCompact.of_isClosed_subset isCompact_Icc (hFclosed i)
      ((hFsub i).trans Ioo_subset_Icc_self)
  rw [hTransportImage]
  apply IsSigmaCompact.image hEvaluationContinuous
  exact sigmaCompactProd
    (sigmaCompactInterOpen hGamma hOffDiagonalOpen)
    (sigmaCompactIoo 0 1)

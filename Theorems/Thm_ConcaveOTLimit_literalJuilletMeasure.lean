import Definitions.Def_LiteralJuilletExcursion
import Theorems.Thm_ConcaveOTLimit_existsMeasurableFullMeasureSubsetOfAe
import Theorems.Thm_ConcaveOTLimit_goodIncreasingCrossingLevelEqOfAtomlessAt
import Mathlib.MeasureTheory.Constructions.Polish.Basic

open MeasureTheory Set

namespace ConcaveOTLimit

private theorem goodDecreasingCrossingLevelEqOfAtomlessAt
    (mu nu : FiniteMeasure Real) (x h : Real)
    (hAtomlessAt : (nu : Measure Real) {x} = 0)
    (hCrossing : IsGoodDecreasingCrossing mu nu x h) :
    h = signedCumulative mu nu x := by
  have hCumulative (z : Real) :
      signedCumulative nu mu z = -signedCumulative mu nu z := by
    simp only [signedCumulative]
    ring
  have hCumulativeLeft (z : Real) :
      signedCumulativeLeft nu mu z =
        -signedCumulativeLeft mu nu z := by
    simp only [signedCumulativeLeft]
    ring
  have hGraphNeg {z k : Real}
      (hk : (z, k) ∈ generalizedCumulativeGraph mu nu) :
      (z, -k) ∈ generalizedCumulativeGraph nu mu := by
    change
      -k ∈
        uIcc (signedCumulativeLeft nu mu z)
          (signedCumulative nu mu z)
    rw [hCumulative, hCumulativeLeft, ← image_neg_uIcc]
    exact ⟨k, hk, rfl⟩
  have hReflected :
      IsGoodIncreasingCrossing nu mu x (-h) := by
    rcases hCrossing with
      ⟨hGraph, epsilon, hEpsilon, hLocal⟩
    refine ⟨hGraphNeg hGraph, epsilon, hEpsilon, ?_⟩
    intro x' h' hx' hxNe hx'Graph
    have hOriginalGraph :
        (x', -h') ∈ generalizedCumulativeGraph mu nu := by
      change
        h' ∈
          uIcc (signedCumulativeLeft nu mu x')
            (signedCumulative nu mu x') at hx'Graph
      rw [hCumulative, hCumulativeLeft, ← image_neg_uIcc]
        at hx'Graph
      rcases hx'Graph with ⟨k, hk, rfl⟩
      simpa only [neg_neg] using hk
    have hNegative := hLocal hx' hxNe hOriginalGraph
    nlinarith
  have hLevel :=
    goodIncreasingCrossingLevelEqOfAtomlessAt
      nu mu x (-h) hAtomlessAt hReflected
  rw [hCumulative] at hLevel
  linarith

private theorem finiteMeasure_atoms_countable
    (mu : FiniteMeasure Real) :
    {x : Real | (mu : Measure Real) {x} ≠ 0}.Countable := by
  simpa only [pos_iff_ne_zero] using
    (Measure.countable_meas_pos_of_disjoint_iUnion
      (μ := (mu : Measure Real))
      (fun x : Real => measurableSet_singleton x)
      (fun x y hxy => disjoint_singleton.mpr hxy))

/-- The first marginal of the literal pair occupation measure is the
occupation measure of its entrance branches. -/
theorem map_fst_literalJuilletExcursionMeasure
    {mu nu : FiniteMeasure Real}
    (data : JuilletCompletedGraphPairingData mu nu) :
    Measure.map Prod.fst (literalJuilletExcursionMeasure data) =
      Measure.sum fun i =>
        Measure.map (data.source i)
          ((volume : Measure Real).restrict (data.active i)) := by
  rw [literalJuilletExcursionMeasure,
    Measure.map_sum measurable_fst.aemeasurable]
  apply Measure.sum_congr
  intro i
  rw [Measure.map_map measurable_fst
    ((data.source_measurable i).prodMk (data.target_measurable i))]
  rfl

/-- The second marginal of the literal pair occupation measure is the
occupation measure of its exit branches. -/
theorem map_snd_literalJuilletExcursionMeasure
    {mu nu : FiniteMeasure Real}
    (data : JuilletCompletedGraphPairingData mu nu) :
    Measure.map Prod.snd (literalJuilletExcursionMeasure data) =
      Measure.sum fun i =>
        Measure.map (data.target i)
          ((volume : Measure Real).restrict (data.active i)) := by
  rw [literalJuilletExcursionMeasure,
    Measure.map_sum measurable_snd.aemeasurable]
  apply Measure.sum_congr
  intro i
  rw [Measure.map_map measurable_snd
    ((data.source_measurable i).prodMk (data.target_measurable i))]
  rfl

/-- Every atom in the literal completed-graph construction is forward. -/
theorem literalJuilletExcursionMeasure_forward
    {mu nu : FiniteMeasure Real}
    (data : JuilletCompletedGraphPairingData mu nu) :
    ∀ᵐ z ∂literalJuilletExcursionMeasure data, z.1 <= z.2 := by
  rw [literalJuilletExcursionMeasure, Measure.ae_sum_iff]
  intro i
  apply
    (ae_map_iff
      ((data.source_measurable i).prodMk
        (data.target_measurable i)).aemeasurable
      (measurableSet_le measurable_fst measurable_snd)).2
  filter_upwards
    [ae_restrict_of_ae data.paired_ae,
      ae_restrict_mem (data.active_measurable i)] with h hPaired hActive
  exact (hPaired i hActive).2.2.2.1.le

/-- The literal completed-graph occupation measure is carried by the
canonical Juillet routes. -/
theorem literalJuilletExcursionMeasure_supportedOnCanonicalRouteSet
    {mu nu : FiniteMeasure Real}
    (data : JuilletCompletedGraphPairingData mu nu) :
    ∀ᵐ z ∂literalJuilletExcursionMeasure data,
      z ∈ juilletCanonicalRouteSet mu nu := by
  rw [literalJuilletExcursionMeasure, Measure.ae_sum_iff]
  obtain ⟨G, hGMeasurable, hGNull, hPairedOnG⟩ :=
    existsMeasurableFullMeasureSubsetOfAe
      (volume : Measure Real) data.paired_ae
  have hGAe : ∀ᵐ h ∂(volume : Measure Real), h ∈ G := by
    simpa only [compl_compl] using
      (compl_mem_ae_iff.2 hGNull)
  let muAtoms : Set Real :=
    {x | (mu : Measure Real) {x} ≠ 0}
  let nuAtoms : Set Real :=
    {x | (nu : Measure Real) {x} ≠ 0}
  have hMuAtomsCountable : muAtoms.Countable := by
    simpa only [muAtoms] using finiteMeasure_atoms_countable mu
  have hNuAtomsCountable : nuAtoms.Countable := by
    simpa only [nuAtoms] using finiteMeasure_atoms_countable nu
  have hMuAtomsMeasurable : MeasurableSet muAtoms :=
    hMuAtomsCountable.measurableSet
  have hNuAtomsMeasurable : MeasurableSet nuAtoms :=
    hNuAtomsCountable.measurableSet
  intro i
  let pair : Real -> Real × Real :=
    fun h => (data.source i h, data.target i h)
  have hPairMeasurable : Measurable pair :=
    (data.source_measurable i).prodMk (data.target_measurable i)
  let D : Set Real := G ∩ data.active i
  let sourceDiffuse : Set Real :=
    D ∩ data.source i ⁻¹' muAtomsᶜ
  let targetDiffuse : Set Real :=
    (D ∩ data.source i ⁻¹' muAtoms) ∩
      data.target i ⁻¹' nuAtomsᶜ
  let bothAtomic : Set Real :=
    (D ∩ data.source i ⁻¹' muAtoms) ∩
      data.target i ⁻¹' nuAtoms
  have hDMeasurable : MeasurableSet D :=
    hGMeasurable.inter (data.active_measurable i)
  have hSourceDiffuseMeasurable : MeasurableSet sourceDiffuse :=
    hDMeasurable.inter
      (hMuAtomsMeasurable.compl.preimage
        (data.source_measurable i))
  have hTargetDiffuseMeasurable : MeasurableSet targetDiffuse :=
    (hDMeasurable.inter
      (hMuAtomsMeasurable.preimage
        (data.source_measurable i))).inter
      (hNuAtomsMeasurable.compl.preimage
        (data.target_measurable i))
  have hPairedOnD {h : Real} (hh : h ∈ D) :
      pair h ∈ juilletCompletedGraphPairFiber mu nu h :=
    hPairedOnG h hh.1 i hh.2
  have hPairInjOnSourceDiffuse :
      Set.InjOn pair sourceDiffuse := by
    intro h hh k hk hPairEq
    have hSourceEq :
        data.source i h = data.source i k :=
      congrArg Prod.fst hPairEq
    have hNoSourceAtomH :
        (mu : Measure Real) {data.source i h} = 0 := by
      simpa only [muAtoms, mem_preimage, mem_compl_iff, mem_setOf_eq,
        not_ne_iff]
        using hh.2
    have hNoSourceAtomK :
        (mu : Measure Real) {data.source i k} = 0 := by
      simpa only [muAtoms, mem_preimage, mem_compl_iff, mem_setOf_eq,
        not_ne_iff]
        using hk.2
    have hLevelH :=
      goodIncreasingCrossingLevelEqOfAtomlessAt
        mu nu (data.source i h) h hNoSourceAtomH
          (hPairedOnD hh.1).2.1
    have hLevelK :=
      goodIncreasingCrossingLevelEqOfAtomlessAt
        mu nu (data.source i k) k hNoSourceAtomK
          (hPairedOnD hk.1).2.1
    calc
      h = signedCumulative mu nu (data.source i h) := hLevelH
      _ = signedCumulative mu nu (data.source i k) := by
        rw [hSourceEq]
      _ = k := hLevelK.symm
  have hPairInjOnTargetDiffuse :
      Set.InjOn pair targetDiffuse := by
    intro h hh k hk hPairEq
    have hTargetEq :
        data.target i h = data.target i k :=
      congrArg Prod.snd hPairEq
    have hNoTargetAtomH :
        (nu : Measure Real) {data.target i h} = 0 := by
      simpa only [nuAtoms, mem_preimage, mem_compl_iff, mem_setOf_eq,
        not_ne_iff]
        using hh.2
    have hNoTargetAtomK :
        (nu : Measure Real) {data.target i k} = 0 := by
      simpa only [nuAtoms, mem_preimage, mem_compl_iff, mem_setOf_eq,
        not_ne_iff]
        using hk.2
    have hLevelH :=
      goodDecreasingCrossingLevelEqOfAtomlessAt
        mu nu (data.target i h) h hNoTargetAtomH
          (hPairedOnD hh.1.1).2.2.1
    have hLevelK :=
      goodDecreasingCrossingLevelEqOfAtomlessAt
        mu nu (data.target i k) k hNoTargetAtomK
          (hPairedOnD hk.1.1).2.2.1
    calc
      h = signedCumulative mu nu (data.target i h) := hLevelH
      _ = signedCumulative mu nu (data.target i k) := by
        rw [hTargetEq]
      _ = k := hLevelK.symm
  let sourceCarrier : Set (Real × Real) :=
    pair '' sourceDiffuse
  let targetCarrier : Set (Real × Real) :=
    pair '' targetDiffuse
  let atomicCarrier : Set (Real × Real) :=
    pair '' bothAtomic
  have hSourceCarrierMeasurable : MeasurableSet sourceCarrier :=
    hSourceDiffuseMeasurable.image_of_measurable_injOn
      hPairMeasurable hPairInjOnSourceDiffuse
  have hTargetCarrierMeasurable : MeasurableSet targetCarrier :=
    hTargetDiffuseMeasurable.image_of_measurable_injOn
      hPairMeasurable hPairInjOnTargetDiffuse
  have hAtomicCarrierCountable : atomicCarrier.Countable := by
    apply (hMuAtomsCountable.prod hNuAtomsCountable).mono
    rintro z ⟨h, hh, rfl⟩
    exact ⟨hh.1.2, hh.2⟩
  have hAtomicCarrierMeasurable : MeasurableSet atomicCarrier :=
    hAtomicCarrierCountable.measurableSet
  let carrier : Set (Real × Real) :=
    sourceCarrier ∪ targetCarrier ∪ atomicCarrier
  have hCarrierMeasurable : MeasurableSet carrier :=
    (hSourceCarrierMeasurable.union hTargetCarrierMeasurable).union
      hAtomicCarrierMeasurable
  have hPairMemCarrier {h : Real} (hh : h ∈ D) :
      pair h ∈ carrier := by
    by_cases hSourceAtom : data.source i h ∈ muAtoms
    · by_cases hTargetAtom : data.target i h ∈ nuAtoms
      · exact Or.inr ⟨h,
          ⟨⟨hh, hSourceAtom⟩, hTargetAtom⟩, rfl⟩
      · exact Or.inl (Or.inr ⟨h,
          ⟨⟨hh, hSourceAtom⟩, hTargetAtom⟩, rfl⟩)
    · exact Or.inl (Or.inl ⟨h,
        ⟨hh, hSourceAtom⟩, rfl⟩)
  have hPairMemRoute {h : Real} (hh : h ∈ D) :
      pair h ∈ juilletCanonicalRouteSet mu nu := by
    refine ⟨h, ?_⟩
    simpa only [juilletCompletedGraphPairFiber, mem_setOf_eq, pair]
      using hPairedOnD hh
  have hCarrierSubset :
      carrier ⊆ juilletCanonicalRouteSet mu nu := by
    intro z hz
    rcases hz with (hz | hz) | hz
    · rcases hz with ⟨h, hh, rfl⟩
      exact hPairMemRoute hh.1
    · rcases hz with ⟨h, hh, rfl⟩
      exact hPairMemRoute hh.1.1
    · rcases hz with ⟨h, hh, rfl⟩
      exact hPairMemRoute hh.1.1
  have hRestrictedCarrier :
      ∀ᵐ h ∂(volume : Measure Real).restrict (data.active i),
        pair h ∈ carrier := by
    filter_upwards
      [ae_restrict_of_ae hGAe,
        ae_restrict_mem (data.active_measurable i)] with h hG hActive
    exact hPairMemCarrier ⟨hG, hActive⟩
  have hMappedCarrier :
      ∀ᵐ z ∂Measure.map pair
          ((volume : Measure Real).restrict (data.active i)),
        z ∈ carrier :=
    (ae_map_iff hPairMeasurable.aemeasurable hCarrierMeasurable).2
      hRestrictedCarrier
  exact hMappedCarrier.mono fun z hz => hCarrierSubset hz

/-- Exact entrance and exit occupation identities turn pairing data into a
finite literal coupling. -/
theorem exists_literalJuilletExcursionPlan_of_pairing_marginals
    {mu nu : FiniteMeasure Real}
    (data : JuilletCompletedGraphPairingData mu nu)
    (hSource :
      Measure.map Prod.fst (literalJuilletExcursionMeasure data) =
        (mu : Measure Real))
    (hTarget :
      Measure.map Prod.snd (literalJuilletExcursionMeasure data) =
        (nu : Measure Real)) :
    ∃ gamma : FiniteMeasure (Real × Real),
      IsLiteralJuilletExcursionPlan mu nu gamma := by
  let rho : Measure (Real × Real) :=
    literalJuilletExcursionMeasure data
  have hRhoUniv :
      rho univ = (mu : Measure Real) univ := by
    calc
      rho univ = Measure.map Prod.fst rho univ := by
        rw [Measure.map_apply measurable_fst MeasurableSet.univ]
        simp
      _ = (mu : Measure Real) univ := by
        rw [hSource]
  letI : IsFiniteMeasure rho :=
    ⟨by
      rw [hRhoUniv]
      exact measure_lt_top (mu : Measure Real) univ⟩
  let gamma : FiniteMeasure (Real × Real) := ⟨rho, inferInstance⟩
  refine ⟨gamma, ?_, data, rfl⟩
  constructor
  · change gamma.map Prod.fst = mu
    apply Subtype.ext
    exact hSource
  · change gamma.map Prod.snd = nu
    apply Subtype.ext
    exact hTarget

end ConcaveOTLimit

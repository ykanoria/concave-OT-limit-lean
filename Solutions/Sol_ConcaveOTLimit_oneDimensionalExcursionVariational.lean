import Definitions.Def_JuilletCanonicalRoutes
import Theorems.Thm_ConcaveOTLimit_existsMeasurableFullMassLexicographicSupportOfSecondaryMinimizer
import Theorems.Thm_ConcaveOTLimit_existsStrictMonotoneArchSupportOfJuilletExcursionPlan
import Theorems.Thm_ConcaveOTLimit_oneDimensionalExcursionVariationalOfSupportAndIdentification

open MeasureTheory Set

open ConcaveOTLimit

private theorem measurePreservingFst
    {mu nu : FiniteMeasure Real} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.fst
      (gamma.plan : Measure (Real × Real)) (mu : Measure Real) := by
  refine ⟨measurable_fst, ?_⟩
  simpa [firstMarginal] using congrArg
    (fun eta : FiniteMeasure Real => (eta : Measure Real)) gamma.property.1

private theorem measurePreservingSnd
    {mu nu : FiniteMeasure Real} (gamma : FiniteCoupling mu nu) :
    MeasurePreserving Prod.snd
      (gamma.plan : Measure (Real × Real)) (nu : Measure Real) := by
  refine ⟨measurable_snd, ?_⟩
  simpa [secondMarginal] using congrArg
    (fun eta : FiniteMeasure Real => (eta : Measure Real)) gamma.property.2

private theorem signedCumulative_eq_forwardCrossing
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (hForward : IsForwardPlan gamma) (c : Real) :
    signedCumulative mu nu c =
      ((gamma.plan : Measure (Real × Real))
        (Iic c ×ˢ Ioi c)).toReal := by
  let sourceLeft : Set (Real × Real) := {z | z.1 <= c}
  let targetLeft : Set (Real × Real) := {z | z.2 <= c}
  let crossing : Set (Real × Real) := Iic c ×ˢ Ioi c
  have hTargetMeasurable : MeasurableSet targetLeft :=
    measurableSet_le measurable_snd measurable_const
  have hSourceDiff : sourceLeft \ targetLeft = crossing := by
    ext z
    simp only [sourceLeft, targetLeft, crossing, mem_diff, mem_setOf_eq,
      mem_prod, mem_Iic, mem_Ioi, not_le]
  have hSourceMeasure :
      (gamma.plan : Measure (Real × Real)) sourceLeft =
        (mu : Measure Real) (Iic c) := by
    calc
      (gamma.plan : Measure (Real × Real)) sourceLeft =
          Measure.map Prod.fst
            (gamma.plan : Measure (Real × Real)) (Iic c) := by
        rw [Measure.map_apply measurable_fst measurableSet_Iic]
        rfl
      _ = (mu : Measure Real) (Iic c) := by
        rw [(measurePreservingFst gamma).map_eq]
  have hTargetMeasure :
      (gamma.plan : Measure (Real × Real)) targetLeft =
        (nu : Measure Real) (Iic c) := by
    calc
      (gamma.plan : Measure (Real × Real)) targetLeft =
          Measure.map Prod.snd
            (gamma.plan : Measure (Real × Real)) (Iic c) := by
        rw [Measure.map_apply measurable_snd measurableSet_Iic]
        rfl
      _ = (nu : Measure Real) (Iic c) := by
        rw [(measurePreservingSnd gamma).map_eq]
  have hTargetInter :
      (gamma.plan : Measure (Real × Real))
          (sourceLeft ∩ targetLeft) =
        (gamma.plan : Measure (Real × Real)) targetLeft := by
    apply measure_congr
    filter_upwards [hForward] with z hz
    change
      (z.1 <= c ∧ z.2 <= c) = (z.2 <= c)
    apply propext
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨hz.trans h, h⟩
  have hDecomp :
      (gamma.plan : Measure (Real × Real)) crossing +
          (gamma.plan : Measure (Real × Real)) targetLeft =
        (gamma.plan : Measure (Real × Real)) sourceLeft := by
    rw [← hTargetInter, ← hSourceDiff]
    exact measure_diff_add_inter sourceLeft hTargetMeasurable
  rw [signedCumulative, ← hSourceMeasure, ← hTargetMeasure, ← hDecomp,
    ENNReal.toReal_add
      (measure_ne_top (gamma.plan : Measure (Real × Real)) crossing)
      (measure_ne_top (gamma.plan : Measure (Real × Real)) targetLeft)]
  simp only [add_sub_cancel_right, crossing]

private theorem forwardArchSubsetOfRightOverlap
    {x y x' y' : Real}
    (hxy : x < y)
    (hx'y : x' < y)
    (hyy' : y < y')
    (hNoCross : ArchesDoNotCross (x, y) (x', y')) :
    uIcc x y ⊆ uIcc x' y' := by
  rcases hNoCross with
    hDisjoint | hSingleton | hSubset | hSubsetRev
  · exact False.elim
      (Set.disjoint_left.mp hDisjoint right_mem_uIcc
        (mem_uIcc_of_le hx'y.le hyy'.le))
  · obtain ⟨z, hz⟩ := hSingleton
    have hLower : max x x' < y := max_lt hxy hx'y
    obtain ⟨c, hcLower, hcy⟩ := exists_between hLower
    have hxc : x <= c := (le_max_left x x').trans hcLower.le
    have hx'c : x' <= c := (le_max_right x x').trans hcLower.le
    have hcFirst : c ∈ uIcc x y :=
      mem_uIcc_of_le hxc hcy.le
    have hcSecond : c ∈ uIcc x' y' :=
      mem_uIcc_of_le hx'c (hcy.trans hyy').le
    have hyFirst : y ∈ uIcc x y := right_mem_uIcc
    have hySecond : y ∈ uIcc x' y' :=
      mem_uIcc_of_le hx'y.le hyy'.le
    have hcz : c = z := by
      have : c ∈ ({z} : Set Real) := by
        rw [← hz]
        exact ⟨hcFirst, hcSecond⟩
      simpa only [mem_singleton_iff] using this
    have hyz : y = z := by
      have : y ∈ ({z} : Set Real) := by
        rw [← hz]
        exact ⟨hyFirst, hySecond⟩
      simpa only [mem_singleton_iff] using this
    exact False.elim (hcy.ne (hcz.trans hyz.symm))
  · exact hSubset
  · have hy'Mem :=
      hSubsetRev (right_mem_uIcc : y' ∈ uIcc x' y')
    rw [uIcc_of_le hxy.le] at hy'Mem
    exact False.elim ((not_le_of_gt hyy') hy'Mem.2)

/-- In a laminar family of forward arches, some cut of `[a,b]` is crossed
only by arches spanning the whole interval. -/
private theorem existsMonotoneArchSpanningCut
    (S : Set (Real × Real))
    (hNoCross :
      ∀ p ∈ S, ∀ q ∈ S, ArchesDoNotCross p q)
    {a b : Real} (hab : a <= b) :
    ∃ t ∈ Icc a b,
      ∀ {x y : Real}, (x, y) ∈ S ->
        x < t -> t < y -> x <= a ∧ b < y := by
  let endpoints : Set Real :=
    {r |
      ∃ x : Real,
        (x, r) ∈ S ∧ x < a ∧ a < r ∧
          ¬ (x <= a ∧ b < r)}
  by_cases hEndpoints : endpoints.Nonempty
  · have hEndpointLe : ∀ ⦃r⦄, r ∈ endpoints -> r <= b := by
      intro r hr
      rcases hr with ⟨x, hxS, hxa, har, hLocal⟩
      exact le_of_not_gt fun hbr => hLocal ⟨hxa.le, hbr⟩
    have hBounded : BddAbove endpoints := ⟨b, hEndpointLe⟩
    let t := sSup endpoints
    have htUpper : t <= b :=
      csSup_le hEndpoints hEndpointLe
    have hEndpointWitness := hEndpoints
    obtain ⟨r, hr⟩ := hEndpointWitness
    have hrLe : r <= t := le_csSup hBounded hr
    have hat : a <= t := by
      rcases hr with ⟨x, hxS, hxa, har, hLocal⟩
      exact (har.trans_le hrLe).le
    refine ⟨t, ⟨hat, htUpper⟩, ?_⟩
    intro x y hxyS hxt hty
    have hxa : x < a := by
      by_contra hNot
      have hax : a <= x := le_of_not_gt hNot
      obtain ⟨r, hrEndpoints, hxr⟩ :=
        exists_lt_of_lt_csSup hEndpoints hxt
      rcases hrEndpoints with
        ⟨x', hx'rS, hx'a, har, hLocal⟩
      have hrLe : r <= t := le_csSup hBounded
        ⟨x', hx'rS, hx'a, har, hLocal⟩
      have hrY : r < y := hrLe.trans_lt hty
      have hSubset :
          uIcc x' r ⊆ uIcc x y :=
        forwardArchSubsetOfRightOverlap
          (hx'a.trans har) hxr hrY
          (hNoCross (x', r) hx'rS (x, y) hxyS)
      have hx'Mem :=
        hSubset (left_mem_uIcc : x' ∈ uIcc x' r)
      rw [uIcc_of_le (hxt.trans hty).le] at hx'Mem
      exact (not_le_of_gt hx'a) (hax.trans hx'Mem.1)
    refine ⟨hxa.le, ?_⟩
    by_contra hNot
    have hyb : y <= b := le_of_not_gt hNot
    have hyEndpoints : y ∈ endpoints := by
      refine ⟨x, hxyS, hxa, hat.trans_lt hty, ?_⟩
      intro hSpan
      exact (not_lt_of_ge hyb) hSpan.2
    exact (not_lt_of_ge (le_csSup hBounded hyEndpoints)) hty
  · refine ⟨a, ⟨le_rfl, hab⟩, ?_⟩
    intro x y hxyS hxa hay
    refine ⟨hxa.le, ?_⟩
    by_contra hNot
    have hyb : y <= b := le_of_not_gt hNot
    have hyEndpoints : y ∈ endpoints := by
      exact ⟨x, hxyS, hxa, hay,
        fun hSpan => (not_lt_of_ge hyb) hSpan.2⟩
    exact hEndpoints ⟨y, hyEndpoints⟩

private theorem existsSpanningCrossingCut
    {mu nu : FiniteMeasure Real}
    (gamma : FiniteCoupling mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (S : Set (Real × Real))
    (hFull : IsSupported gamma S)
    (hStrict :
      ∀ {x y : Real}, (x, y) ∈ S -> x < y)
    (hMonotone : IsMonotoneArchSet S)
    {a b : Real} (hab : a <= b) :
    ∃ t ∈ Icc a b,
      (gamma.plan : Measure (Real × Real)) (Iic a ×ˢ Ioi b) =
        (gamma.plan : Measure (Real × Real)) (Iic t ×ˢ Ioi t) := by
  obtain ⟨t, ht, hCut⟩ :=
    existsMonotoneArchSpanningCut S
      (fun p hp q hq => (hMonotone p hp q hq).1) hab
  have hMuNe : ∀ᵐ x ∂(mu : Measure Real), x ≠ t := by
    rw [ae_iff]
    simpa only [not_ne_iff] using hAtomless t
  have hSourceNe :
      ∀ᵐ z ∂(gamma.plan : Measure (Real × Real)), z.1 ≠ t :=
    (measurePreservingFst gamma).quasiMeasurePreserving.ae hMuNe
  refine ⟨t, ht, ?_⟩
  apply measure_congr
  filter_upwards [hFull, hSourceNe] with z hzS hzNe
  change
    (z.1 <= a ∧ b < z.2) = (z.1 <= t ∧ t < z.2)
  apply propext
  constructor
  · intro hz
    exact ⟨hz.1.trans ht.1, ht.2.trans_lt hz.2⟩
  · intro hz
    exact hCut hzS (lt_of_le_of_ne hz.1 hzNe) hz.2

private theorem crossingMeasureEq
    {mu nu : FiniteMeasure Real}
    (gamma eta : FiniteCoupling mu nu)
    (hGammaForward : IsForwardPlan gamma)
    (hEtaForward : IsForwardPlan eta)
    (t : Real) :
    (gamma.plan : Measure (Real × Real)) (Iic t ×ˢ Ioi t) =
      (eta.plan : Measure (Real × Real)) (Iic t ×ˢ Ioi t) := by
  apply
    (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top (gamma.plan : Measure (Real × Real))
        (Iic t ×ˢ Ioi t))
      (measure_ne_top (eta.plan : Measure (Real × Real))
        (Iic t ×ˢ Ioi t))).mp
  exact
    (signedCumulative_eq_forwardCrossing gamma hGammaForward t).symm.trans
      (signedCumulative_eq_forwardCrossing eta hEtaForward t)

private theorem spanningMeasureEq
    {mu nu : FiniteMeasure Real}
    (hAtomless : IsAtomlessFinite mu)
    (gamma eta : FiniteCoupling mu nu)
    (hGammaForward : IsForwardPlan gamma)
    (hEtaForward : IsForwardPlan eta)
    (S R : Set (Real × Real))
    (hSFull : IsSupported gamma S)
    (hSStrict :
      ∀ {x y : Real}, (x, y) ∈ S -> x < y)
    (hSMonotone : IsMonotoneArchSet S)
    (hRFull : IsSupported eta R)
    (hRStrict :
      ∀ {x y : Real}, (x, y) ∈ R -> x < y)
    (hRMonotone : IsMonotoneArchSet R)
    {a b : Real} (hab : a <= b) :
    (gamma.plan : Measure (Real × Real)) (Iic a ×ˢ Ioi b) =
      (eta.plan : Measure (Real × Real)) (Iic a ×ˢ Ioi b) := by
  obtain ⟨s, hs, hGammaCut⟩ :=
    existsSpanningCrossingCut gamma hAtomless S
      hSFull hSStrict hSMonotone hab
  obtain ⟨t, ht, hEtaCut⟩ :=
    existsSpanningCrossingCut eta hAtomless R
      hRFull hRStrict hRMonotone hab
  have hSpanSubset :
      ∀ {r : Real}, r ∈ Icc a b ->
        Iic a ×ˢ Ioi b ⊆ Iic r ×ˢ Ioi r := by
    intro r hr z hz
    exact ⟨hz.1.trans hr.1, hr.2.trans_lt hz.2⟩
  apply le_antisymm
  · calc
      (gamma.plan : Measure (Real × Real)) (Iic a ×ˢ Ioi b) <=
          (gamma.plan : Measure (Real × Real)) (Iic t ×ˢ Ioi t) :=
        measure_mono (hSpanSubset ht)
      _ = (eta.plan : Measure (Real × Real)) (Iic t ×ˢ Ioi t) :=
        crossingMeasureEq gamma eta hGammaForward hEtaForward t
      _ = (eta.plan : Measure (Real × Real)) (Iic a ×ˢ Ioi b) :=
        hEtaCut.symm
  · calc
      (eta.plan : Measure (Real × Real)) (Iic a ×ˢ Ioi b) <=
          (eta.plan : Measure (Real × Real)) (Iic s ×ˢ Ioi s) :=
        measure_mono (hSpanSubset hs)
      _ = (gamma.plan : Measure (Real × Real)) (Iic s ×ˢ Ioi s) :=
        (crossingMeasureEq gamma eta
          hGammaForward hEtaForward s).symm
      _ = (gamma.plan : Measure (Real × Real)) (Iic a ×ˢ Ioi b) :=
        hGammaCut.symm

private theorem measure_eq_of_Iic_prod_Iic
    (rho eta : Measure (Real × Real))
    [IsFiniteMeasure rho] [IsFiniteMeasure eta]
    (hRect :
      ∀ a b : Real,
        rho (Iic a ×ˢ Iic b) = eta (Iic a ×ˢ Iic b)) :
    rho = eta := by
  have hFirstSlice :
      ∀ a : Real,
        Measure.map Prod.snd
            (rho.restrict (Prod.fst ⁻¹' Iic a)) =
          Measure.map Prod.snd
            (eta.restrict (Prod.fst ⁻¹' Iic a)) := by
    intro a
    apply Measure.ext_of_Iic
    intro b
    rw [Measure.map_apply measurable_snd measurableSet_Iic,
      Measure.map_apply measurable_snd measurableSet_Iic,
      Measure.restrict_apply
        (measurableSet_Iic.preimage measurable_snd),
      Measure.restrict_apply
        (measurableSet_Iic.preimage measurable_snd)]
    have hSet :
        Prod.snd ⁻¹' Iic b ∩ Prod.fst ⁻¹' Iic a =
          Iic a ×ˢ Iic b := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_prod]
      tauto
    rw [hSet, hRect a b]
  have hIicFirst :
      ∀ (a : Real) {B : Set Real}, MeasurableSet B ->
        rho (Iic a ×ˢ B) = eta (Iic a ×ˢ B) := by
    intro a B hB
    have hRhoSet :
        Prod.snd ⁻¹' B ∩ Prod.fst ⁻¹' Iic a =
          Iic a ×ˢ B := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_prod]
      tauto
    calc
      rho (Iic a ×ˢ B) =
          Measure.map Prod.snd
            (rho.restrict (Prod.fst ⁻¹' Iic a)) B := by
        rw [Measure.map_apply measurable_snd hB,
          Measure.restrict_apply (hB.preimage measurable_snd),
          hRhoSet]
      _ = Measure.map Prod.snd
            (eta.restrict (Prod.fst ⁻¹' Iic a)) B := by
        rw [hFirstSlice a]
      _ = eta (Iic a ×ˢ B) := by
        rw [Measure.map_apply measurable_snd hB,
          Measure.restrict_apply (hB.preimage measurable_snd),
          hRhoSet]
  apply Measure.ext_prod
  intro A B hA hB
  let rhoB : Measure Real :=
    Measure.map Prod.fst (rho.restrict (Prod.snd ⁻¹' B))
  let etaB : Measure Real :=
    Measure.map Prod.fst (eta.restrict (Prod.snd ⁻¹' B))
  have hSecondSlice : rhoB = etaB := by
    apply Measure.ext_of_Iic
    intro a
    have hSet :
        Prod.fst ⁻¹' Iic a ∩ Prod.snd ⁻¹' B =
          Iic a ×ˢ B := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_prod]
    calc
      rhoB (Iic a) = rho (Iic a ×ˢ B) := by
        dsimp only [rhoB]
        rw [Measure.map_apply measurable_fst measurableSet_Iic,
          Measure.restrict_apply
            (measurableSet_Iic.preimage measurable_fst), hSet]
      _ = eta (Iic a ×ˢ B) := hIicFirst a hB
      _ = etaB (Iic a) := by
        dsimp only [etaB]
        rw [Measure.map_apply measurable_fst measurableSet_Iic,
          Measure.restrict_apply
            (measurableSet_Iic.preimage measurable_fst), hSet]
  have hSet :
      Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' B = A ×ˢ B := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_prod]
  calc
    rho (A ×ˢ B) = rhoB A := by
      dsimp only [rhoB]
      rw [Measure.map_apply measurable_fst hA,
        Measure.restrict_apply (hA.preimage measurable_fst), hSet]
    _ = etaB A := by rw [hSecondSlice]
    _ = eta (A ×ˢ B) := by
      dsimp only [etaB]
      rw [Measure.map_apply measurable_fst hA,
        Measure.restrict_apply (hA.preimage measurable_fst), hSet]

private theorem juilletExcursionPlan_unique
    {mu nu : FiniteMeasure Real}
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (gamma eta : FiniteCoupling mu nu)
    (hGamma : IsJuilletExcursionPlan mu nu gamma.plan)
    (hEta : IsJuilletExcursionPlan mu nu eta.plan) :
    gamma = eta := by
  have hGammaForward : IsForwardPlan gamma :=
    isForwardPlanOfJuilletExcursionPlan hAtomless hOrder hGamma
  have hEtaForward : IsForwardPlan eta :=
    isForwardPlanOfJuilletExcursionPlan hAtomless hOrder hEta
  obtain ⟨S, hSMeasurable, hSFull, hSStrict, hSMonotone⟩ :=
    existsStrictMonotoneArchSupportOfJuilletExcursionPlan
      hSingular hAtomless hOrder hGamma
  obtain ⟨R, hRMeasurable, hRFull, hRStrict, hRMonotone⟩ :=
    existsStrictMonotoneArchSupportOfJuilletExcursionPlan
      hSingular hAtomless hOrder hEta
  apply Subtype.ext
  apply FiniteMeasure.toMeasure_injective
  apply measure_eq_of_Iic_prod_Iic
  intro a b
  by_cases hab : a <= b
  · have hSpan :=
      spanningMeasureEq hAtomless gamma eta
        hGammaForward hEtaForward S R
        hSFull hSStrict hSMonotone
        hRFull hRStrict hRMonotone hab
    let source : Set (Real × Real) := Prod.fst ⁻¹' Iic a
    let span : Set (Real × Real) := Iic a ×ˢ Ioi b
    have hSpanSubset : span ⊆ source := by
      intro z hz
      exact hz.1
    have hSpanMeasurable : MeasurableSet span :=
      measurableSet_Iic.prod measurableSet_Ioi
    have hDiff : source \ span = Iic a ×ˢ Iic b := by
      ext z
      simp only [source, span, mem_diff, mem_preimage, mem_Iic,
        mem_prod, mem_Ioi, not_lt]
      constructor
      · intro hz
        refine ⟨hz.1, le_of_not_gt ?_⟩
        intro hbz
        exact hz.2 ⟨hz.1, hbz⟩
      · intro hz
        refine ⟨hz.1, ?_⟩
        intro hSpan
        exact (not_lt_of_ge hz.2) hSpan.2
    have hGammaSource :
        (gamma.plan : Measure (Real × Real)) source =
          (mu : Measure Real) (Iic a) := by
      calc
        (gamma.plan : Measure (Real × Real)) source =
            Measure.map Prod.fst
              (gamma.plan : Measure (Real × Real)) (Iic a) := by
          rw [Measure.map_apply measurable_fst measurableSet_Iic]
        _ = (mu : Measure Real) (Iic a) := by
          rw [(measurePreservingFst gamma).map_eq]
    have hEtaSource :
        (eta.plan : Measure (Real × Real)) source =
          (mu : Measure Real) (Iic a) := by
      calc
        (eta.plan : Measure (Real × Real)) source =
            Measure.map Prod.fst
              (eta.plan : Measure (Real × Real)) (Iic a) := by
          rw [Measure.map_apply measurable_fst measurableSet_Iic]
        _ = (mu : Measure Real) (Iic a) := by
          rw [(measurePreservingFst eta).map_eq]
    calc
      (gamma.plan : Measure (Real × Real)) (Iic a ×ˢ Iic b) =
          (gamma.plan : Measure (Real × Real)) source -
            (gamma.plan : Measure (Real × Real)) span := by
        rw [← hDiff]
        exact measure_diff hSpanSubset hSpanMeasurable.nullMeasurableSet
          (measure_ne_top (gamma.plan : Measure (Real × Real)) span)
      _ = (mu : Measure Real) (Iic a) -
            (gamma.plan : Measure (Real × Real)) span := by
        rw [hGammaSource]
      _ = (mu : Measure Real) (Iic a) -
            (eta.plan : Measure (Real × Real)) span := by
        rw [hSpan]
      _ = (eta.plan : Measure (Real × Real)) source -
            (eta.plan : Measure (Real × Real)) span := by
        rw [hEtaSource]
      _ = (eta.plan : Measure (Real × Real)) (Iic a ×ˢ Iic b) := by
        rw [← hDiff]
        exact
          (measure_diff hSpanSubset hSpanMeasurable.nullMeasurableSet
            (measure_ne_top (eta.plan : Measure (Real × Real)) span)).symm
  · have hba : b < a := lt_of_not_ge hab
    have hGammaRect :
        (gamma.plan : Measure (Real × Real)) (Iic a ×ˢ Iic b) =
          (nu : Measure Real) (Iic b) := by
      calc
        (gamma.plan : Measure (Real × Real)) (Iic a ×ˢ Iic b) =
            (gamma.plan : Measure (Real × Real))
              (Prod.snd ⁻¹' Iic b) := by
          apply measure_congr
          filter_upwards [hGammaForward] with z hz
          change
            (z.1 <= a ∧ z.2 <= b) = (z.2 <= b)
          apply propext
          constructor
          · exact fun h => h.2
          · intro h
            exact ⟨hz.trans (h.trans hba.le), h⟩
        _ = Measure.map Prod.snd
              (gamma.plan : Measure (Real × Real)) (Iic b) := by
          rw [Measure.map_apply measurable_snd measurableSet_Iic]
        _ = (nu : Measure Real) (Iic b) := by
          rw [(measurePreservingSnd gamma).map_eq]
    have hEtaRect :
        (eta.plan : Measure (Real × Real)) (Iic a ×ˢ Iic b) =
          (nu : Measure Real) (Iic b) := by
      calc
        (eta.plan : Measure (Real × Real)) (Iic a ×ˢ Iic b) =
            (eta.plan : Measure (Real × Real))
              (Prod.snd ⁻¹' Iic b) := by
          apply measure_congr
          filter_upwards [hEtaForward] with z hz
          change
            (z.1 <= a ∧ z.2 <= b) = (z.2 <= b)
          apply propext
          constructor
          · exact fun h => h.2
          · intro h
            exact ⟨hz.trans (h.trans hba.le), h⟩
        _ = Measure.map Prod.snd
              (eta.plan : Measure (Real × Real)) (Iic b) := by
          rw [Measure.map_apply measurable_snd measurableSet_Iic]
        _ = (nu : Measure Real) (Iic b) := by
          rw [(measurePreservingSnd eta).map_eq]
    exact hGammaRect.trans hEtaRect.symm

/-- Paper Theorem 6: for atomless, mutually singular, stochastically ordered
one-dimensional marginals, Juillet's excursion coupling is the common
minimizer of every admissible concave secondary objective on the forward
(equivalently distance-optimal) face, uniquely so for strict concavity. -/
theorem solution
    (mu nu : FiniteMeasure Real)
    (hMass : mu.mass = nu.mass)
    (hPositive : 0 < mu.mass)
    (hFirstMu :
      Integrable (fun x : Real => |x|) (mu : Measure Real))
    (hFirstNu :
      Integrable (fun y : Real => |y|) (nu : Measure Real))
    (hSingular : FiniteMutuallySingular mu nu)
    (hAtomless : IsAtomlessFinite mu)
    (hOrder : StochasticallyDominates nu mu)
    (gammaEC : FiniteCoupling mu nu)
    (hEC : IsJuilletExcursionPlan mu nu gammaEC.plan) :
    IsForwardPlan gammaEC /\
      {gamma : FiniteCoupling mu nu | IsForwardPlan gamma} =
        distanceOptimalFace mu nu /\
      (∀ profile : Real -> Real,
        AdmissibleConcaveProfile profile ->
          IsMinimizerOn
            {gamma : FiniteCoupling mu nu | IsForwardPlan gamma}
            (profileCost profile) gammaEC) /\
      (∀ profile : Real -> Real,
        AdmissibleStrictlyConcaveProfile profile ->
          IsUniqueMinimizerOn
            {gamma : FiniteCoupling mu nu | IsForwardPlan gamma}
            (profileCost profile) gammaEC) := by
  apply oneDimensionalExcursionVariationalOfSupportAndIdentification
    hFirstMu hFirstNu hSingular hAtomless hOrder gammaEC hEC
  · intro profile hProfile gamma hMin hForward
    exact
      existsMeasurableFullMassLexicographicSupportOfSecondaryMinimizer
        hProfile hFirstMu hFirstNu hSingular hMin hForward
  · intro gamma hGamma
    exact juilletExcursionPlan_unique
      hSingular hAtomless hOrder gamma gammaEC hGamma hEC

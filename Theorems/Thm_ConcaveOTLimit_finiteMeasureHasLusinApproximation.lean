import Definitions.Def_ConcaveOTLimitModel

open MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace ConcaveOTLimit

/-- A measurable map from a finite Borel pseudometric measure space is
continuous on closed sets with arbitrarily small complement. -/
theorem finiteMeasureHasLusinApproximation
    {X Y : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [SecondCountableTopology Y]
    (mu : FiniteMeasure X) {T : X -> Y} (hT : Measurable T) :
    forall delta : ENNReal, delta ≠ 0 ->
      exists K : Set X, IsClosed K /\ ContinuousOn T K /\
        (mu : Measure X) Kᶜ < delta := by
  intro delta hdelta
  let B := TopologicalSpace.countableBasis Y
  let A : B -> Set X := fun b => T ⁻¹' (b : Set Y)
  have hA : forall b, MeasurableSet (A b) := fun b =>
    hT (TopologicalSpace.isOpen_of_mem_countableBasis b.2).measurableSet
  obtain ⟨epsilon : B -> ENNReal, hepsilon_pos, hepsilon_sum⟩ :=
    ENNReal.exists_pos_sum_of_countable' hdelta B
  have hepsilon_half : forall b, epsilon b / 2 ≠ 0 := fun b =>
    ENNReal.div_ne_zero.mpr
      ⟨(hepsilon_pos b).ne', ENNReal.ofNat_ne_top⟩
  choose F hF_sub hF_closed hF_small using fun b =>
    (hA b).exists_isClosed_diff_lt
      (measure_ne_top (mu : Measure X) _) (hepsilon_half b)
  choose G hG_sub hG_closed hG_small using fun b =>
    (hA b).compl.exists_isClosed_diff_lt
      (measure_ne_top (mu : Measure X) _) (hepsilon_half b)
  let K : Set X := ⋂ b, F b ∪ G b
  refine
    ⟨K, isClosed_iInter fun b => (hF_closed b).union (hG_closed b),
      ?_, ?_⟩
  · rw [(TopologicalSpace.isBasis_countableBasis Y).continuousOn_iff]
    intro t ht
    let b : B := ⟨t, ht⟩
    refine ⟨(G b)ᶜ, (hG_closed b).isOpen_compl, ?_⟩
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff]
    constructor
    · rintro ⟨hxA, hxK⟩
      refine ⟨?_, hxK⟩
      intro hxG
      exact (hG_sub b hxG) hxA
    · rintro ⟨hxG, hxK⟩
      have hx_union : x ∈ F b ∪ G b := mem_iInter.mp hxK b
      rcases hx_union with hxF | hxG'
      · exact ⟨hF_sub b hxF, hxK⟩
      · exact (hxG hxG').elim
  · change (mu : Measure X) ((⋂ b, F b ∪ G b)ᶜ) < delta
    rw [compl_iInter]
    refine ((measure_iUnion_le _).trans ?_).trans_lt hepsilon_sum
    apply ENNReal.tsum_le_tsum
    intro b
    exact (calc
      (mu : Measure X) ((F b ∪ G b)ᶜ)
          <= (mu : Measure X) (A b \ F b) +
              (mu : Measure X) ((A b)ᶜ \ G b) := by
            apply (measure_mono ?_).trans (measure_union_le _ _)
            intro x hx
            by_cases hxA : x ∈ A b
            · exact Or.inl ⟨hxA, fun hxF => hx (Or.inl hxF)⟩
            · exact Or.inr ⟨hxA, fun hxG => hx (Or.inr hxG)⟩
      _ < epsilon b / 2 + epsilon b / 2 :=
        ENNReal.add_lt_add (hF_small b) (hG_small b)
      _ = epsilon b := ENNReal.add_halves (epsilon b)).le

end ConcaveOTLimit

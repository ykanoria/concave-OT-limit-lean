import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Set Topology

/-- A nonzero derivative determines the orientation with which the graph
strictly crosses its value at the base point. -/
theorem solution
    {g : Real -> Real} {d x : Real}
    (hg : HasDerivAt g d x) (hd : d ≠ 0) :
    (0 < d ∧
      ∃ epsilon, 0 < epsilon ∧
        ∀ y : Real,
          y ∈ Ioo (x - epsilon) (x + epsilon) ->
            y ≠ x -> 0 < (g y - g x) * (y - x)) ∨
    (d < 0 ∧
      ∃ epsilon, 0 < epsilon ∧
        ∀ y : Real,
          y ∈ Ioo (x - epsilon) (x + epsilon) ->
            y ≠ x -> (g y - g x) * (y - x) < 0) := by
  rcases lt_or_gt_of_ne hd with hdneg | hdpos
  · refine Or.inr ⟨hdneg, ?_⟩
    have hslopeWithin :
        ∀ᶠ y in nhdsWithin x {x}ᶜ, slope g x y < 0 :=
      hg.tendsto_slope.eventually (Iio_mem_nhds hdneg)
    have hslopeNear :
        ∀ᶠ y in nhds x, y ≠ x -> slope g x y < 0 := by
      simpa only [mem_compl_iff, mem_singleton_iff] using
        (eventually_nhdsWithin_iff.mp hslopeWithin)
    obtain ⟨epsilon, hepsilon, hnear⟩ :=
      Metric.eventually_nhds_iff_ball.mp hslopeNear
    refine ⟨epsilon, hepsilon, ?_⟩
    intro y hy hyx
    have hslope : slope g x y < 0 := hnear y (by
      simpa only [Real.ball_eq_Ioo] using hy) hyx
    rw [slope_def_field] at hslope
    rcases (div_neg_iff.mp hslope) with
      ⟨hnum, hden⟩ | ⟨hnum, hden⟩
    · exact mul_neg_of_pos_of_neg hnum hden
    · exact mul_neg_of_neg_of_pos hnum hden
  · refine Or.inl ⟨hdpos, ?_⟩
    have hslopeWithin :
        ∀ᶠ y in nhdsWithin x {x}ᶜ, 0 < slope g x y :=
      hg.tendsto_slope.eventually (Ioi_mem_nhds hdpos)
    have hslopeNear :
        ∀ᶠ y in nhds x, y ≠ x -> 0 < slope g x y := by
      simpa only [mem_compl_iff, mem_singleton_iff] using
        (eventually_nhdsWithin_iff.mp hslopeWithin)
    obtain ⟨epsilon, hepsilon, hnear⟩ :=
      Metric.eventually_nhds_iff_ball.mp hslopeNear
    refine ⟨epsilon, hepsilon, ?_⟩
    intro y hy hyx
    have hslope : 0 < slope g x y := hnear y (by
      simpa only [Real.ball_eq_Ioo] using hy) hyx
    rw [slope_def_field] at hslope
    rcases (div_pos_iff.mp hslope) with
      ⟨hnum, hden⟩ | ⟨hnum, hden⟩
    · exact mul_pos hnum hden
    · exact mul_pos_of_neg_of_neg hnum hden

import Definitions.Def_ConcaveOTLimitModel

open MeasureTheory Set

namespace ConcaveOTLimit

/-- Centering a profile cost and dividing by a positive parameter preserves
its global minimizers. -/
theorem isMinimizerOn_rescaledProfileCost
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    {mu nu : FiniteMeasure E} {family : Real -> Real -> Real}
    {epsilon : Real} (hEpsilonPos : 0 < epsilon)
    {gamma : FiniteCoupling mu nu}
    (hMinimizer : IsProfileMinimizer (family epsilon) gamma) :
    IsMinimizerOn Set.univ
      (rescaledProfileCost family epsilon) gamma := by
  rcases hMinimizer with ⟨_hMember, hMinimal⟩
  refine ⟨mem_univ gamma, ?_⟩
  intro eta _heta
  unfold rescaledProfileCost
  exact (div_le_div_iff_of_pos_right hEpsilonPos).2
    (sub_le_sub_right (hMinimal eta (mem_univ eta))
      (minimalDistanceCost mu nu))

end ConcaveOTLimit

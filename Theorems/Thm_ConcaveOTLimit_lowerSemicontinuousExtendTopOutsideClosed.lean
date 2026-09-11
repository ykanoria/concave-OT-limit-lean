import Mathlib.Topology.Semicontinuity.Basic

open Set

namespace ConcaveOTLimit

open scoped Classical in
/-- Extending an `ENNReal`-valued lower-semicontinuous function by `top`
outside a closed set preserves lower semicontinuity. -/
theorem lowerSemicontinuousExtendTopOutsideClosed
    {Omega : Type*} [TopologicalSpace Omega]
    {f : Omega -> ENNReal} {F : Set Omega}
    (hf : LowerSemicontinuous f) (hF : IsClosed F) :
    LowerSemicontinuous (fun x => if x ∈ F then f x else ⊤) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  by_cases hy : y = ⊤
  · subst y
    simp
  · have hpreimage :
        (fun x => if x ∈ F then f x else ⊤) ⁻¹' Iic y =
          F ∩ f ⁻¹' Iic y := by
      ext x
      by_cases hx : x ∈ F <;> simp [hx, hy]
    rw [hpreimage]
    exact hF.inter (hf.isClosed_preimage y)

end ConcaveOTLimit

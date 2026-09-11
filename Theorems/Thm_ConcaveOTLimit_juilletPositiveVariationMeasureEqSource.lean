import Definitions.Def_JuilletPositiveVariation

open MeasureTheory Set

namespace ConcaveOTLimit

/-- Under mutual singularity, the positive Jordan variation of `mu - nu` is
exactly `mu`. -/
theorem juilletPositiveVariationMeasureEqSource
    {mu nu : FiniteMeasure Real}
    (hSingular : FiniteMutuallySingular mu nu) :
    juilletPositiveVariationMeasure mu nu = (mu : Measure Real) := by
  have hMutuallySingular :
      (mu : Measure Real) ⟂ₘ (nu : Measure Real) := by
    rcases hSingular with ⟨A, hA, hMu, hNu⟩
    exact ⟨Aᶜ, hA.compl, hMu, by simpa only [compl_compl] using hNu⟩
  let jordan : JordanDecomposition Real :=
    { posPart := (mu : Measure Real)
      negPart := (nu : Measure Real)
      mutuallySingular := hMutuallySingular }
  have hSigned :
      juilletSignedMeasure mu nu = jordan.toSignedMeasure := by
    rfl
  rw [juilletPositiveVariationMeasure,
    SignedMeasure.toJordanDecomposition_eq hSigned]

end ConcaveOTLimit

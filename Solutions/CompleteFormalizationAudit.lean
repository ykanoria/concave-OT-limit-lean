import Theorems.Thm_ConcaveOTLimit_completePaperMainTheorems
import Theorems.Thm_ConcaveOTLimit_canonicalRaywiseReplacement
import Theorems.Thm_ConcaveOTLimit_literalJuilletConstructionUnconditional
import Theorems.Thm_ConcaveOTLimit_mainConvergence
import Mathlib.Util.AssertNoSorry

/-!
# Complete formalization audit

The declarations below include the unconditional producers for the
OT-specific inputs used by the two paper-facing main theorems. This file
rejects proof placeholders and dependencies on nonstandard axioms.
-/

open Lean Meta Elab Command

private meta def isStandardAxiom (name : Name) : Bool :=
  name == ``propext ||
    name == ``Classical.choice ||
    name == ``Quot.sound

/-- Reject a declaration if its dependency closure contains a custom axiom. -/
elab "assert_only_standard_axioms " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let axioms ← Lean.collectAxioms name
  for axiomName in axioms do
    unless isStandardAxiom axiomName do
      throwError "{n} depends on nonstandard axiom {axiomName}"

assert_no_sorry ConcaveOTLimit.distanceContactCharacterization
assert_only_standard_axioms ConcaveOTLimit.distanceContactCharacterization

assert_no_sorry ConcaveOTLimit.borelMaximalRayMap
assert_only_standard_axioms ConcaveOTLimit.borelMaximalRayMap

assert_no_sorry ConcaveOTLimit.contactSetRayRegularity
assert_only_standard_axioms ConcaveOTLimit.contactSetRayRegularity

assert_no_sorry ConcaveOTLimit.literalJuilletConstructionPremise_unconditional
assert_only_standard_axioms
  ConcaveOTLimit.literalJuilletConstructionPremise_unconditional

assert_no_sorry ConcaveOTLimit.literalJuilletIdentificationPremise_unconditional
assert_only_standard_axioms
  ConcaveOTLimit.literalJuilletIdentificationPremise_unconditional

assert_no_sorry ConcaveOTLimit.oneDimensionalExcursionVariational
assert_only_standard_axioms
  ConcaveOTLimit.oneDimensionalExcursionVariational

assert_no_sorry ConcaveOTLimit.canonicalRaywiseReplacement
assert_only_standard_axioms ConcaveOTLimit.canonicalRaywiseReplacement

assert_no_sorry ConcaveOTLimit.concaveGammaSelection
assert_only_standard_axioms ConcaveOTLimit.concaveGammaSelection

assert_no_sorry ConcaveOTLimit.uniqueSecondaryMinimizer
assert_only_standard_axioms ConcaveOTLimit.uniqueSecondaryMinimizer

assert_no_sorry ConcaveOTLimit.logarithmicSecondaryUniqueness
assert_only_standard_axioms ConcaveOTLimit.logarithmicSecondaryUniqueness

assert_no_sorry ConcaveOTLimit.perturbationMinimizerGraphPremise
assert_only_standard_axioms
  ConcaveOTLimit.perturbationMinimizerGraphPremise

assert_no_sorry ConcaveOTLimit.nonempty_powerOptimizerFamily
assert_only_standard_axioms ConcaveOTLimit.nonempty_powerOptimizerFamily

assert_no_sorry ConcaveOTLimit.mainConvergence
assert_only_standard_axioms ConcaveOTLimit.mainConvergence

assert_no_sorry ConcaveOTLimit.mainConvergenceRaywise_every
assert_only_standard_axioms ConcaveOTLimit.mainConvergenceRaywise_every

assert_no_sorry ConcaveOTLimit.powerCostConvergence
assert_only_standard_axioms ConcaveOTLimit.powerCostConvergence

assert_no_sorry ConcaveOTLimit.powerCostConvergenceRaywiseFaithful_every
assert_only_standard_axioms
  ConcaveOTLimit.powerCostConvergenceRaywiseFaithful_every

assert_no_sorry ConcaveOTLimit.PaperStatements.concaveCostMainTheorem
assert_only_standard_axioms
  ConcaveOTLimit.PaperStatements.concaveCostMainTheorem

assert_no_sorry ConcaveOTLimit.PaperStatements.powerCostMainTheorem
assert_only_standard_axioms
  ConcaveOTLimit.PaperStatements.powerCostMainTheorem

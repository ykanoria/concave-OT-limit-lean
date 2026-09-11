import Definitions.Def_ConcaveOTLimitModel

open MeasureTheory Set

open ConcaveOTLimit

theorem solution
    {Omega : Type*} [MeasurableSpace Omega]
    (gamma : FiniteMeasure Omega) {U V : Set Omega}
    (hMeasurable : MeasurableSet U ∧ MeasurableSet V)
    (hDisjoint : Disjoint U V) (c : NNReal)
    (hCoeffU : c * (gamma.restrict U).mass ≤ 1)
    (hCoeffV : c * (gamma.restrict V).mass ≤ 1) :
    (((c * (gamma.restrict V).mass) • gamma.restrict U +
        (c * (gamma.restrict U).mass) • gamma.restrict V :
          FiniteMeasure Omega) : Measure Omega) ≤
      (gamma : Measure Omega) := by
  have smul_le_self_measure
      (tau : FiniteMeasure Omega) (d : NNReal) (hd : d ≤ 1) :
      ((d • tau : FiniteMeasure Omega) : Measure Omega) ≤
        (tau : Measure Omega) := by
    apply Measure.le_iff'.2
    intro s
    simp only [FiniteMeasure.toMeasure_smul,
      Measure.coe_nnreal_smul_apply]
    exact mul_le_of_le_one_left bot_le (by exact_mod_cast hd)
  have hU :
      (((c * (gamma.restrict V).mass) • gamma.restrict U :
          FiniteMeasure Omega) : Measure Omega) ≤
        (gamma.restrict U : Measure Omega) :=
    smul_le_self_measure (gamma.restrict U)
      (c * (gamma.restrict V).mass) hCoeffV
  have hV :
      (((c * (gamma.restrict U).mass) • gamma.restrict V :
          FiniteMeasure Omega) : Measure Omega) ≤
        (gamma.restrict V : Measure Omega) :=
    smul_le_self_measure (gamma.restrict V)
      (c * (gamma.restrict U).mass) hCoeffU
  calc
    (((c * (gamma.restrict V).mass) • gamma.restrict U +
        (c * (gamma.restrict U).mass) • gamma.restrict V :
          FiniteMeasure Omega) : Measure Omega) ≤
        (gamma.restrict U : Measure Omega) +
          (gamma.restrict V : Measure Omega) :=
      add_le_add hU hV
    _ = ((gamma.restrict U + gamma.restrict V :
          FiniteMeasure Omega) : Measure Omega) :=
      (FiniteMeasure.toMeasure_add _ _).symm
    _ = (gamma.restrict (U ∪ V) : Measure Omega) := by
      exact congrArg
        (fun tau : FiniteMeasure Omega => (tau : Measure Omega))
        (FiniteMeasure.restrict_union hDisjoint hMeasurable.2).symm
    _ ≤ (gamma : Measure Omega) := Measure.restrict_le_self

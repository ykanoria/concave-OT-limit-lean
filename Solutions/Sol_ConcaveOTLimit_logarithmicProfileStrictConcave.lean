import Definitions.Def_ConcaveOTLimitModel

open Set

open ConcaveOTLimit

theorem solution :
    StrictConcaveOn Real (Ici 0) logarithmicProfile := by
  unfold logarithmicProfile
  exact Real.strictConcaveOn_negMulLog

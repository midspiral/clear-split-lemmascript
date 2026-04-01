import «logic.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct expenseDelta by
  unfold Pure.expenseDelta; loom_solve

prove_correct computeBalance by
  loom_solve

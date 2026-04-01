import «logic.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct expenseDelta by
  unfold Pure.expenseDelta; loom_solve

prove_correct computeBalance by
  loom_solve

-- Helper: pushing a valid expense preserves allExpensesValid
theorem allExpensesValid_push (expenses : Array Expense) (e : Expense) (mc : Int)
    (hprev : Pure.allExpensesValid expenses expenses.size mc = true)
    (hvalid : Pure.validExpense e mc = true) :
    Pure.allExpensesValid (expenses.push e) (expenses.push e).size mc = true := by
  sorry

-- Helper: pushing a valid settlement preserves allSettlementsValid
theorem allSettlementsValid_push (settlements : Array Settlement) (s : Settlement) (mc : Int)
    (hprev : Pure.allSettlementsValid settlements settlements.size mc = true)
    (hvalid : Pure.validSettlement s mc = true) :
    Pure.allSettlementsValid (settlements.push s) (settlements.push s).size mc = true := by
  sorry

section StepProof
set_option maxHeartbeats 400000
set_option loom.solver "custom"
set_option hygiene false in
macro_rules
| `(tactic|loom_solver) => `(tactic| first
  | grind
  | omega
  | (cases action with
     | addExpense e => simp_all [Pure.inv, Pure.validExpense, allExpensesValid_push]; omega
     | addSettlement s => simp_all [Pure.inv, Pure.validSettlement, allSettlementsValid_push]; omega))
prove_correct step by
  unfold Pure.step
  loom_solve
  -- remaining goal: inv preserved
  -- TODO: prove step preserves inv (needs allExpensesValid_push and allSettlementsValid_push)
  all_goals sorry
end StepProof

import «logic.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct expenseDelta by
  unfold Pure.expenseDelta; loom_solve

prove_correct computeBalance by
  loom_solve

-- Helper: pushing a valid expense preserves allExpensesValid
-- Key lemma: arr.push e at index < arr.size equals arr at that index
private theorem push_getElem!_lt {α : Type} [Inhabited α] (arr : Array α) (e : α) (i : Nat)
    (hi : i < arr.size) : (arr.push e)[i]! = arr[i]! := by
  have h1 : i < (arr.push e).size := by simp [Array.size_push]; omega
  simp only [h1, hi, getElem!_pos, Array.getElem_push, ↓reduceDIte]

private theorem push_getElem!_last {α : Type} [Inhabited α] (arr : Array α) (e : α) :
    (arr.push e)[arr.size]! = e := by
  have h1 : arr.size < (arr.push e).size := by simp [Array.size_push]
  simp only [h1, getElem!_pos, Array.getElem_push, show ¬(arr.size < arr.size) from by omega, ↓reduceDIte]

-- allExpensesValid over a prefix doesn't change when we push beyond
theorem allExpensesValid_prefix (arr : Array Expense) (e : Expense) (n : Nat) (mc : Int)
    (hn : n ≤ arr.size) :
    Pure.allExpensesValid (arr.push e) n mc = Pure.allExpensesValid arr n mc := by
  induction n with
  | zero => simp [Pure.allExpensesValid]
  | succ k ih =>
    have hk : k ≤ arr.size := by omega
    unfold Pure.allExpensesValid
    simp only [show ¬(k + 1 = 0) from by omega, ↓reduceIte, show k + 1 - 1 = k from by omega]
    rw [push_getElem!_lt _ _ _ (by omega), ih hk]

theorem allExpensesValid_push (expenses : Array Expense) (e : Expense) (mc : Int)
    (hprev : Pure.allExpensesValid expenses expenses.size mc = true)
    (hvalid : Pure.validExpense e mc = true) :
    Pure.allExpensesValid (expenses.push e) (expenses.push e).size mc = true := by
  unfold Pure.allExpensesValid
  simp only [Array.size_push, show ¬(expenses.size + 1 = 0) from by omega, ↓reduceIte,
             show expenses.size + 1 - 1 = expenses.size from by omega]
  rw [push_getElem!_last, allExpensesValid_prefix _ _ _ _ (le_refl _)]
  simp [hvalid, hprev]

theorem allSettlementsValid_prefix (arr : Array Settlement) (s : Settlement) (n : Nat) (mc : Int)
    (hn : n ≤ arr.size) :
    Pure.allSettlementsValid (arr.push s) n mc = Pure.allSettlementsValid arr n mc := by
  induction n with
  | zero => simp [Pure.allSettlementsValid]
  | succ k ih =>
    have hk : k ≤ arr.size := by omega
    unfold Pure.allSettlementsValid
    simp only [show ¬(k + 1 = 0) from by omega, ↓reduceIte, show k + 1 - 1 = k from by omega]
    rw [push_getElem!_lt _ _ _ (by omega), ih hk]

theorem allSettlementsValid_push (settlements : Array Settlement) (s : Settlement) (mc : Int)
    (hprev : Pure.allSettlementsValid settlements settlements.size mc = true)
    (hvalid : Pure.validSettlement s mc = true) :
    Pure.allSettlementsValid (settlements.push s) (settlements.push s).size mc = true := by
  unfold Pure.allSettlementsValid
  simp only [Array.size_push, show ¬(settlements.size + 1 = 0) from by omega, ↓reduceIte,
             show settlements.size + 1 - 1 = settlements.size from by omega]
  rw [push_getElem!_last, allSettlementsValid_prefix _ _ _ _ (le_refl _)]
  simp [hvalid, hprev]

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
  cases action with
  | addExpense e =>
    simp only [Pure.inv, Pure.validExpense] at *
    split <;> (try split) <;> (try split) <;> simp_all <;>
    rw [show model.expenses.size + 1 = (model.expenses.push e).size from by simp [Array.size_push]]
    exact allExpensesValid_push model.expenses e _ (by tauto) (by simp [Pure.validExpense]; omega)
  | addSettlement s =>
    simp only [Pure.inv, Pure.validSettlement] at *
    split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp_all <;>
    rw [show model.settlements.size + 1 = (model.settlements.push s).size from by simp [Array.size_push]]
    exact allSettlementsValid_push model.settlements s _ (by tauto) (by simp [Pure.validSettlement]; omega)
end StepProof

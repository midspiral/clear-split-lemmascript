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

-- ═════════════════════════════════════════════════════════════���
-- Conservation theorems
-- ══════════════════════════════════════════════════════════════

/-- Sum of expenseDelta across members [0, n) for a single expense -/
def sumDeltas (paidBy : Int) (amount : Int) (shares : Array Int) (n : Nat) : Int :=
  if n = 0 then 0
  else sumDeltas paidBy amount shares (n - 1) + Pure.expenseDelta paidBy amount shares[n - 1]! (n - 1)

-- When paidBy is NOT in [0, n), sum = -sumTo
theorem sumDeltas_no_payer (paidBy : Int) (amount : Int) (shares : Array Int) (n : Nat)
    (h : ¬(0 ≤ paidBy ∧ paidBy < ↑n)) :
    sumDeltas paidBy amount shares n = -Pure.sumTo shares n := by
  induction n with
  | zero => unfold sumDeltas Pure.sumTo; omega
  | succ k ih =>
    unfold sumDeltas Pure.sumTo Pure.expenseDelta
    have hk : ¬(k + 1 = 0) := by omega
    have hk' : ¬(paidBy = ↑(k + 1) - 1) := by omega
    have hprev : ¬(0 ≤ paidBy ∧ paidBy < ↑k) := by omega
    simp [hk, hk']; rw [ih hprev]; omega

-- When paidBy IS in [0, n), sum = amount - sumTo
theorem sumDeltas_with_payer (paidBy : Int) (amount : Int) (shares : Array Int) (n : Nat)
    (h : 0 ≤ paidBy ∧ paidBy < ↑n) :
    sumDeltas paidBy amount shares n = amount - Pure.sumTo shares n := by
  induction n with
  | zero => omega
  | succ k ih =>
    unfold sumDeltas Pure.sumTo Pure.expenseDelta
    have hk : ¬(k + 1 = 0) := by omega
    by_cases hk' : paidBy = ↑(k + 1) - 1
    · simp [hk, hk']
      have hnotk : ¬(0 ≤ (↑k : Int) ∧ (↑k : Int) < ↑k) := by omega
      rw [sumDeltas_no_payer _ _ _ _ hnotk]; omega
    · simp [hk, hk']
      have : 0 ≤ paidBy ∧ paidBy < ↑k := by omega
      rw [ih this]; omega

/-- Single-expense conservation: if shares sum to amount, deltas across all members sum to zero -/
theorem single_expense_conservation
    (paidBy : Int) (amount : Int) (shares : Array Int) (n : Nat)
    (hpayer : 0 ≤ paidBy ∧ paidBy < ↑n)
    (hshares : Pure.sumTo shares n = amount) :
    sumDeltas paidBy amount shares n = 0 := by
  rw [sumDeltas_with_payer _ _ _ _ hpayer, hshares]; omega

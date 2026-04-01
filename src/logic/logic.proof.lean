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

-- ══════════════════════════════════════════════════════════════
-- Global conservation: sum of all balances across all members is zero
-- ══════════════════════════════════════════════════════════════

/-- Balance for member m from one expense -/
def balanceFromExpense (e : Expense) (m : Nat) : Int :=
  Pure.expenseDelta e.paidBy e.amount e.shares[m]! m

/-- Balance for member m from all expenses [0, k) -/
def balanceFromExpenses (expenses : Array Expense) (k : Nat) (m : Nat) : Int :=
  if k = 0 then 0
  else balanceFromExpenses expenses (k - 1) m + balanceFromExpense expenses[k - 1]! m

/-- Sum of balances across members [0, n) from all expenses -/
def sumBalances (expenses : Array Expense) (numExpenses : Nat) (n : Nat) : Int :=
  if n = 0 then 0
  else sumBalances expenses numExpenses (n - 1) + balanceFromExpenses expenses numExpenses (n - 1)

/-- Sum of member deltas [0, n) for one expense -/
def sumMemberDeltas (e : Expense) (n : Nat) : Int :=
  sumDeltas e.paidBy e.amount e.shares n

/-- Sum-swap: sumBalances = sum over expenses of sumMemberDeltas.
    Each expense contributes zero (by single_expense_conservation),
    so the total is zero. -/

-- First prove the swap for one expense added
theorem balanceFromExpenses_split (expenses : Array Expense) (k : Nat) (m : Nat) :
    balanceFromExpenses expenses (k + 1) m =
    balanceFromExpenses expenses k m + balanceFromExpense expenses[k]! m := by
  conv_lhs => unfold balanceFromExpenses
  simp [show ¬(k + 1 = 0) from by omega, show k + 1 - 1 = k from by omega]

-- sumBalances distributes over expenses: adding one expense adds sumMemberDeltas
theorem sumBalances_zero_expenses (expenses : Array Expense) (n : Nat) :
    sumBalances expenses 0 n = 0 := by
  induction n with
  | zero => simp [sumBalances]
  | succ k ih => simp [sumBalances, balanceFromExpenses, ih]

-- Key swap: sumBalances with k+1 expenses = sumBalances with k + sumMemberDeltas of expense k
theorem sumBalances_add_expense (expenses : Array Expense) (k n : Nat) :
    sumBalances expenses (k + 1) n = sumBalances expenses k n + sumMemberDeltas expenses[k]! n := by
  induction n with
  | zero => simp [sumBalances, sumMemberDeltas, sumDeltas]
  | succ m ih =>
    -- LHS: sumBalances expenses (k+1) (m+1) = sumBalances expenses (k+1) m + balanceFromExpenses expenses (k+1) m
    -- RHS: sumBalances expenses k (m+1) + sumMemberDeltas expenses[k]! (m+1)
    --     = (sumBalances expenses k m + balanceFromExpenses expenses k m) + (sumMemberDeltas expenses[k]! m + expenseDelta ...)
    -- By ih: sumBalances expenses (k+1) m = sumBalances expenses k m + sumMemberDeltas expenses[k]! m
    -- Need: balanceFromExpenses expenses (k+1) m = balanceFromExpenses expenses k m + balanceFromExpense expenses[k]! m
    -- which is balanceFromExpenses_split
    conv_lhs => unfold sumBalances
    simp only [show ¬(m + 1 = 0) from by omega, show m + 1 - 1 = m from by omega, ↓reduceIte]
    rw [balanceFromExpenses_split, ih]
    have hbal : sumBalances expenses k (m + 1) =
      sumBalances expenses k m + balanceFromExpenses expenses k m := by
        conv_lhs => unfold sumBalances
        simp [show ¬(m + 1 = 0) from by omega, show m + 1 - 1 = m from by omega]
    rw [hbal]
    unfold sumMemberDeltas
    have hsplit : sumDeltas expenses[k]!.paidBy expenses[k]!.amount expenses[k]!.shares (m + 1) =
      sumDeltas expenses[k]!.paidBy expenses[k]!.amount expenses[k]!.shares m +
      Pure.expenseDelta expenses[k]!.paidBy expenses[k]!.amount expenses[k]!.shares[m]! ↑m := by
        conv_lhs => unfold sumDeltas
        simp [show ¬(m + 1 = 0) from by omega, show m + 1 - 1 = m from by omega, show (↑(m + 1) : Int) - 1 = ↑m from by omega]
    rw [hsplit]
    unfold balanceFromExpense
    omega

-- The main conservation theorem
theorem global_conservation (expenses : Array Expense) (numExpenses memberCount : Nat)
    (hvalid : ∀ i : Nat, i < numExpenses →
      0 ≤ expenses[i]!.paidBy ∧ expenses[i]!.paidBy < ↑memberCount ∧
      Pure.sumTo expenses[i]!.shares memberCount = expenses[i]!.amount) :
    sumBalances expenses numExpenses memberCount = 0 := by
  induction numExpenses with
  | zero => exact sumBalances_zero_expenses _ _
  | succ k ih =>
    rw [sumBalances_add_expense]
    have hk := hvalid k (by omega)
    rw [ih (fun i hi => hvalid i (by omega))]
    simp [sumMemberDeltas]
    exact single_expense_conservation _ _ _ _
      ⟨hk.1, hk.2.1⟩ hk.2.2

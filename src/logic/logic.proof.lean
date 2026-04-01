import «logic.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

prove_correct expenseDelta by
  unfold Pure.expenseDelta; loom_solve

prove_correct settlementDelta by
  unfold Pure.settlementDelta; loom_solve

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
theorem allExpensesValid_prefix (arr : Array Expense) (e : Expense) (n : Nat) (mc : Nat)
    (hn : n ≤ arr.size) :
    Pure.allExpensesValid (arr.push e) n mc = Pure.allExpensesValid arr n mc := by
  induction n with
  | zero => simp [Pure.allExpensesValid]
  | succ k ih =>
    have hk : k ≤ arr.size := by omega
    unfold Pure.allExpensesValid
    simp only [show ¬(k + 1 = 0) from by omega, ↓reduceIte, show k + 1 - 1 = k from by omega]
    rw [push_getElem!_lt _ _ _ (by omega), ih hk]

theorem allExpensesValid_push (expenses : Array Expense) (e : Expense) (mc : Nat)
    (hprev : Pure.allExpensesValid expenses expenses.size mc = true)
    (hvalid : Pure.validExpense e mc = true) :
    Pure.allExpensesValid (expenses.push e) (expenses.push e).size mc = true := by
  unfold Pure.allExpensesValid
  simp only [Array.size_push, show ¬(expenses.size + 1 = 0) from by omega, ↓reduceIte,
             show expenses.size + 1 - 1 = expenses.size from by omega]
  rw [push_getElem!_last, allExpensesValid_prefix _ _ _ _ (le_refl _)]
  simp [hvalid, hprev]

theorem allSettlementsValid_prefix (arr : Array Settlement) (s : Settlement) (n : Nat) (mc : Nat)
    (hn : n ≤ arr.size) :
    Pure.allSettlementsValid (arr.push s) n mc = Pure.allSettlementsValid arr n mc := by
  induction n with
  | zero => simp [Pure.allSettlementsValid]
  | succ k ih =>
    have hk : k ≤ arr.size := by omega
    unfold Pure.allSettlementsValid
    simp only [show ¬(k + 1 = 0) from by omega, ↓reduceIte, show k + 1 - 1 = k from by omega]
    rw [push_getElem!_lt _ _ _ (by omega), ih hk]

theorem allSettlementsValid_push (settlements : Array Settlement) (s : Settlement) (mc : Nat)
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
    split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp_all <;>
    (rw [show model.expenses.size + 1 = (model.expenses.push e).size from by simp [Array.size_push]];
     exact allExpensesValid_push model.expenses e model.memberCount (by tauto) (by simp [Pure.validExpense]; tauto))
  | addSettlement s =>
    simp only [Pure.inv, Pure.validSettlement] at *
    split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp_all <;>
    (rw [show model.settlements.size + 1 = (model.settlements.push s).size from by simp [Array.size_push]];
     exact allSettlementsValid_push model.settlements s model.memberCount (by tauto) (by simp [Pure.validSettlement]; omega))
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

-- ══════════════════════════════════════════════════════════════
-- Settlement conservation
-- ══════════════════════════════════════════════════════════════

/-- Sum of settlementDelta across members [0, n) for one settlement -/
def sumSettlementDeltas (from_ to_ amount : Int) (n : Nat) : Int :=
  if n = 0 then 0
  else sumSettlementDeltas from_ to_ amount (n - 1) + Pure.settlementDelta from_ to_ amount (n - 1)

-- When neither from nor to is in [0, n), sum = 0
theorem sumSettlementDeltas_none (from_ to_ amount : Int) (n : Nat)
    (hf : ¬(0 ≤ from_ ∧ from_ < ↑n)) (ht : ¬(0 ≤ to_ ∧ to_ < ↑n)) :
    sumSettlementDeltas from_ to_ amount n = 0 := by
  induction n with
  | zero => simp [sumSettlementDeltas]
  | succ k ih =>
    unfold sumSettlementDeltas Pure.settlementDelta
    simp only [show ¬(k + 1 = 0) from by omega, ↓reduceIte, show k + 1 - 1 = k from by omega]
    have : from_ ≠ ↑k := by omega
    have : to_ ≠ ↑k := by omega
    simp [*]; exact ih (by omega) (by omega)

-- When only from is in [0, n), sum = amount
theorem sumSettlementDeltas_from_only (from_ to_ amount : Int) (n : Nat)
    (hf : 0 ≤ from_ ∧ from_ < ↑n) (ht : ¬(0 ≤ to_ ∧ to_ < ↑n)) :
    sumSettlementDeltas from_ to_ amount n = amount := by
  induction n with
  | zero => omega
  | succ k ih =>
    unfold sumSettlementDeltas Pure.settlementDelta
    simp only [show ¬(k + 1 = 0) from by omega, ↓reduceIte, show k + 1 - 1 = k from by omega]
    have htk : to_ ≠ ↑k := by omega
    by_cases hfk : from_ = ↑k
    · simp [hfk, htk]; exact sumSettlementDeltas_none _ _ _ _ (by omega) (by omega)
    · simp [hfk, htk]; exact ih (by omega) (by omega)

-- When only to is in [0, n), sum = -amount
theorem sumSettlementDeltas_to_only (from_ to_ amount : Int) (n : Nat)
    (hf : ¬(0 ≤ from_ ∧ from_ < ↑n)) (ht : 0 ≤ to_ ∧ to_ < ↑n) :
    sumSettlementDeltas from_ to_ amount n = -amount := by
  induction n with
  | zero => omega
  | succ k ih =>
    unfold sumSettlementDeltas Pure.settlementDelta
    simp only [show ¬(k + 1 = 0) from by omega, ↓reduceIte, show k + 1 - 1 = k from by omega]
    have hfk : from_ ≠ ↑k := by omega
    by_cases htk : to_ = ↑k
    · simp [hfk, htk]; rw [sumSettlementDeltas_none _ _ _ _ (by omega) (by omega)]
    · simp [hfk, htk]; exact ih (by omega) (by omega)

/-- Settlement conservation: from gets +amount, to gets -amount, net zero -/
theorem settlement_conservation (from_ to_ amount : Int) (n : Nat)
    (hfrom : 0 ≤ from_ ∧ from_ < ↑n)
    (hto : 0 ≤ to_ ∧ to_ < ↑n)
    (hne : from_ ≠ to_) :
    sumSettlementDeltas from_ to_ amount n = 0 := by
  induction n with
  | zero => omega
  | succ k ih =>
    unfold sumSettlementDeltas Pure.settlementDelta
    simp only [show ¬(k + 1 = 0) from by omega, ↓reduceIte, show k + 1 - 1 = k from by omega]
    by_cases hfk : from_ = ↑k
    · -- from = k
      simp [hfk, show ↑k ≠ to_ from by omega]
      rw [sumSettlementDeltas_to_only (↑k) to_ amount k (by omega) (by omega)]; omega
    · by_cases htk : to_ = ↑k
      · -- to = k
        simp [hfk, htk]
        rw [sumSettlementDeltas_from_only from_ (↑k) amount k (by omega) (by omega)]; omega
      · -- neither
        simp [hfk, htk]
        exact ih (by omega) (by omega)

-- ══════════════════════════════════════════════════════════════
-- Delta laws
-- ══════════════════════════════════════════════════════════════

/-- Adding an expense changes each member's balance by exactly expenseDelta -/
-- Pushing an expense doesn't change balanceFromExpenses for the prefix
theorem balanceFromExpenses_push_prefix (expenses : Array Expense) (e : Expense) (n : Nat) (m : Nat)
    (hn : n ≤ expenses.size) :
    balanceFromExpenses (expenses.push e) n m = balanceFromExpenses expenses n m := by
  induction n with
  | zero => simp [balanceFromExpenses]
  | succ k ih =>
    conv_lhs => unfold balanceFromExpenses
    conv_rhs => unfold balanceFromExpenses
    simp only [show ¬(k + 1 = 0) from by omega, ↓reduceIte, show k + 1 - 1 = k from by omega]
    rw [push_getElem!_lt _ _ _ (by omega)]
    congr 1; exact ih (by omega)

/-- Adding an expense changes each member's balance by exactly expenseDelta -/
theorem add_expense_delta (expenses : Array Expense) (e : Expense) (m : Nat) :
    balanceFromExpenses (expenses.push e) (expenses.size + 1) m =
    balanceFromExpenses expenses expenses.size m + balanceFromExpense e m := by
  conv_lhs => unfold balanceFromExpenses
  simp only [show ¬(expenses.size + 1 = 0) from by omega, ↓reduceIte,
             show expenses.size + 1 - 1 = expenses.size from by omega]
  rw [push_getElem!_last, balanceFromExpenses_push_prefix _ _ _ _ (le_refl _)]

-- Settlement delta laws:
-- from gets +amount, to gets -amount, others get 0
-- settlementDelta from to amount member =
--   if from = member then amount
--   else if to = member then -amount
--   else 0

theorem settlement_delta_from (from_ to_ amount member : Int) (h : from_ = member) :
    Pure.settlementDelta from_ to_ amount member = amount := by
  unfold Pure.settlementDelta; simp [h]

theorem settlement_delta_to (from_ to_ amount member : Int) (hto : to_ = member) (hne : from_ ≠ member) :
    Pure.settlementDelta from_ to_ amount member = -amount := by
  unfold Pure.settlementDelta; simp [hne, hto]

theorem settlement_delta_other (from_ to_ amount member : Int) (hf : from_ ≠ member) (ht : to_ ≠ member) :
    Pure.settlementDelta from_ to_ amount member = 0 := by
  unfold Pure.settlementDelta; simp [hf, ht]

-- ══════════════════════════════════════════════════════════════
-- Full conservation (expenses + settlements)
-- ══════════════════════════════════════════════════════════════

/-- Balance for member m from one settlement -/
def balanceFromSettlement (s : Settlement) (m : Nat) : Int :=
  Pure.settlementDelta s.«from» s.«to» s.amount m

/-- Balance for member m from all settlements [0, k) -/
def balanceFromSettlements (settlements : Array Settlement) (k : Nat) (m : Nat) : Int :=
  if k = 0 then 0
  else balanceFromSettlements settlements (k - 1) m + balanceFromSettlement settlements[k - 1]! m

/-- Full balance = expenses + settlements -/
def fullBalance (expenses : Array Expense) (numExp : Nat)
    (settlements : Array Settlement) (numSett : Nat) (m : Nat) : Int :=
  balanceFromExpenses expenses numExp m + balanceFromSettlements settlements numSett m

/-- Sum of full balances across members [0, n) -/
def sumFullBalances (expenses : Array Expense) (numExp : Nat)
    (settlements : Array Settlement) (numSett : Nat) (n : Nat) : Int :=
  if n = 0 then 0
  else sumFullBalances expenses numExp settlements numSett (n - 1) +
       fullBalance expenses numExp settlements numSett (n - 1)

-- sumFullBalances = sumBalances (expenses) + sumSettlementBalances
def sumSettlementBalances (settlements : Array Settlement) (numSett : Nat) (n : Nat) : Int :=
  if n = 0 then 0
  else sumSettlementBalances settlements numSett (n - 1) + balanceFromSettlements settlements numSett (n - 1)

theorem sumFullBalances_split (expenses : Array Expense) (numExp : Nat)
    (settlements : Array Settlement) (numSett : Nat) (n : Nat) :
    sumFullBalances expenses numExp settlements numSett n =
    sumBalances expenses numExp n + sumSettlementBalances settlements numSett n := by
  induction n with
  | zero => simp [sumFullBalances, sumBalances, sumSettlementBalances]
  | succ k ih =>
    unfold sumFullBalances sumBalances sumSettlementBalances
    simp only [show ¬(k + 1 = 0) from by omega, ↓reduceIte, show k + 1 - 1 = k from by omega]
    rw [ih]; unfold fullBalance; omega

-- Settlement balance sum across all members is zero (analogous to expense conservation)
def sumSettlementMemberDeltas (s : Settlement) (n : Nat) : Int :=
  sumSettlementDeltas s.«from» s.«to» s.amount n

theorem sumSettlementBalances_zero (settlements : Array Settlement) (n : Nat) :
    sumSettlementBalances settlements 0 n = 0 := by
  induction n with
  | zero => simp [sumSettlementBalances]
  | succ k ih => simp [sumSettlementBalances, balanceFromSettlements, ih]

theorem balanceFromSettlements_split (settlements : Array Settlement) (k : Nat) (m : Nat) :
    balanceFromSettlements settlements (k + 1) m =
    balanceFromSettlements settlements k m + balanceFromSettlement settlements[k]! m := by
  conv_lhs => unfold balanceFromSettlements
  simp [show ¬(k + 1 = 0) from by omega, show k + 1 - 1 = k from by omega]

theorem sumSettlementBalances_add (settlements : Array Settlement) (k n : Nat) :
    sumSettlementBalances settlements (k + 1) n =
    sumSettlementBalances settlements k n + sumSettlementMemberDeltas settlements[k]! n := by
  induction n with
  | zero => simp [sumSettlementBalances, sumSettlementMemberDeltas, sumSettlementDeltas]
  | succ m ih =>
    conv_lhs => unfold sumSettlementBalances
    simp only [show ¬(m + 1 = 0) from by omega, show m + 1 - 1 = m from by omega, ↓reduceIte]
    rw [balanceFromSettlements_split, ih]
    have hbal : sumSettlementBalances settlements k (m + 1) =
      sumSettlementBalances settlements k m + balanceFromSettlements settlements k m := by
        conv_lhs => unfold sumSettlementBalances
        simp [show ¬(m + 1 = 0) from by omega, show m + 1 - 1 = m from by omega]
    rw [hbal]
    unfold sumSettlementMemberDeltas
    have hsplit : sumSettlementDeltas settlements[k]!.«from» settlements[k]!.«to» settlements[k]!.amount (m + 1) =
      sumSettlementDeltas settlements[k]!.«from» settlements[k]!.«to» settlements[k]!.amount m +
      Pure.settlementDelta settlements[k]!.«from» settlements[k]!.«to» settlements[k]!.amount ↑m := by
        conv_lhs => unfold sumSettlementDeltas
        simp [show ¬(m + 1 = 0) from by omega, show m + 1 - 1 = m from by omega, show (↑(m + 1) : Int) - 1 = ↑m from by omega]
    rw [hsplit]; unfold balanceFromSettlement; omega

theorem global_settlement_conservation (settlements : Array Settlement) (numSett memberCount : Nat)
    (hvalid : ∀ i : Nat, i < numSett →
      0 ≤ settlements[i]!.«from» ∧ settlements[i]!.«from» < ↑memberCount ∧
      0 ≤ settlements[i]!.«to» ∧ settlements[i]!.«to» < ↑memberCount ∧
      settlements[i]!.«from» ≠ settlements[i]!.«to») :
    sumSettlementBalances settlements numSett memberCount = 0 := by
  induction numSett with
  | zero => exact sumSettlementBalances_zero _ _
  | succ k ih =>
    rw [sumSettlementBalances_add]
    have hk := hvalid k (by omega)
    rw [ih (fun i hi => hvalid i (by omega))]
    simp [sumSettlementMemberDeltas]
    exact settlement_conservation _ _ _ _ ⟨hk.1, hk.2.1⟩ ⟨hk.2.2.1, hk.2.2.2.1⟩ hk.2.2.2.2

/-- THE FULL CONSERVATION THEOREM:
    For a valid model, the sum of all balances across all members is zero. -/
theorem full_conservation (expenses : Array Expense) (numExp : Nat)
    (settlements : Array Settlement) (numSett : Nat) (memberCount : Nat)
    (hexp : ∀ i : Nat, i < numExp →
      0 ≤ expenses[i]!.paidBy ∧ expenses[i]!.paidBy < ↑memberCount ∧
      Pure.sumTo expenses[i]!.shares memberCount = expenses[i]!.amount)
    (hsett : ∀ i : Nat, i < numSett →
      0 ≤ settlements[i]!.«from» ∧ settlements[i]!.«from» < ↑memberCount ∧
      0 ≤ settlements[i]!.«to» ∧ settlements[i]!.«to» < ↑memberCount ∧
      settlements[i]!.«from» ≠ settlements[i]!.«to») :
    sumFullBalances expenses numExp settlements numSett memberCount = 0 := by
  rw [sumFullBalances_split, global_conservation _ _ _ hexp, global_settlement_conservation _ _ _ hsett]; omega
